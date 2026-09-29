/-
# JSP-000090 — the residue of an odd cycle, and the induction step of Erdős–Pósa

`JSPProblem/Transversal.lean` isolated the whole remaining content of Erdős Problem #73
(Reed 1999) in one research statement, `OddCycleErdosPosa r`: a bound on the odd cycle **packing**
number is a bound on the odd cycle **transversal** number (Reed, Robertson, Seymour, Thomas,
*JCTA-B* 86 (2002) 99–136).  Rounds 35 and 38 attacked it from two sides — the local fan structure
at a shortest odd cycle (`JSPProblem/Fan.lean`) and the branch-vertex deletion
(`JSPProblem/Branch.lean`) — and round 39 fixed the optimality of the constant
(`JSPProblem/Sharp.lean`).

This file is the **global half of the classical Erdős–Pósa proof for odd cycles**, to the extent it
can be made machine-checked with the import slice available.  The classical argument deletes one
odd cycle of a maximum packing and studies the *residue* `G - C`; this file proves every step of
that reduction that does not need connectivity/Menger machinery:

1. **Heredity of the local hypothesis to residues** (`LocIndep.induceFinset`,
   `LocIndep.deleteFinset`): the residue of a graph satisfying Erdős's local hypothesis satisfies
   it as well, with the *same* parameter.
2. **The packing number drops by one in the residue** (`insert_oddCycle_of_delete`,
   `card_add_one_le_of_mem_maxPacking`, `LocIndep.oddCycle_packing_residue_lt`): a packing of the
   residue of an odd cycle, together with that cycle, is a packing of `G`.  Under `LocIndep k`
   this reads `𝒟.card + 1 ≤ k` — the strictly-decreasing quantity which an induction on `k`
   would need.
3. **The residue only sees the rest of the packing** (`residue_hits_rest`): if `𝒞` is a maximum
   packing and `C ∈ 𝒞`, then *every* odd cycle of `G` avoiding `C` meets one of the other `|𝒞| - 1`
   cycles.  This is the cross-intersection statement the induction rests on.
4. **The induction step itself** (`hitsOddCycles_union_cycle`, `closeToBipartite_of_residue`): a
   transversal of the residue, together with `C`, is a transversal of `G`; quantitatively,
   `CloseToBipartite q (G - C)` gives `CloseToBipartite (q + |C|) G`.

   **This is exactly where the classical argument stops in this development**: the `+|C|` term is
   unbounded, and turning it into `+1` (the "absorption" step, which is the content of the
   Reed–Robertson–Seymour–Thomas proof) is not available here.
5. **The `r = 1` case of Erdős–Pósa, in full** (`packing_one_transversal`,
   `closeToBipartite_of_packing_one`, `erdos73On_of_packing_one`): in a graph in which any two
   odd cycles meet, *every* odd cycle is an odd cycle transversal and its residue is bipartite.
   Hence, if such a graph has an odd cycle of at most `ℓ` vertices, `LocIndep k G` forces
   `CloseToBipartite ℓ G` — for every `k`, with a constant that does not grow with `k`
   (compare `erdos73On_of_bounded_odd_girth`, which gives `ℓ * k`).  This is a new instance of the
   headline theorem, and it is *not* covered by the branch-vertex instances: `K_5` has no two
   disjoint odd cycles and is full of branch vertices.
6. **Minimum and minimal transversals** (`IsMinimalTransversal`, `exists_minimalTransversal`,
   `exists_private_oddCycle`): a transversal of minimum cardinality exists, is minimal, and every
   one of its vertices lies **alone** on an odd cycle.  These "private" odd cycles are the objects
   the absorption step of the classical proof has to charge against a maximum packing.
-/

import JSPProblem.Sharp
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-! ### Erdős's local hypothesis is inherited by induced subgraphs and by residues -/

/-- **Erdős's local hypothesis is inherited by an induced subgraph**, with the same parameter:
every vertex set of `G[Y]` carries an independent set of `G` (hence of `G[Y]`) which is large
enough.  This is the formal form of the remark in the header of `JSPProblem/Definitions.lean` that
checking induced subgraphs suffices. -/
theorem LocIndep.of_induceFinset {k : ℕ} (hG : LocIndep k G) (Y : Finset V) :
    LocIndep k (induceFinset G Y) := by
  intro X
  obtain ⟨S, hSX, hSind, hb⟩ := hG X
  refine ⟨S, hSX, ?_, hb⟩
  rw [SimpleGraph.isIndepSet_iff] at hSind ⊢
  intro a ha b hb hne h
  exact hSind ha hb hne (induce_adj.mp h).2.2

/-- **Erdős's local hypothesis is inherited by a residue**, with the same parameter.  So if
`LocIndep k G` and `X` is any set of vertices, `deleteFinset G X` also satisfies `LocIndep k`. -/
theorem LocIndep.of_deleteFinset {k : ℕ} (hG : LocIndep k G) (X : Finset V) :
    LocIndep k (deleteFinset G X) :=
  hG.of_induceFinset _

/-! ### Odd cycles of a residue -/

/-- **An odd cycle of the residue `deleteFinset G C` avoids `C`.**  Indeed all consecutive vertices
of its cyclic ordering are adjacent in the deletion, hence outside `C`. -/
theorem inter_empty_of_isOddCycle_delete {C D : Finset V}
    (hD : IsOddCycle (deleteFinset G C) D) : D ∩ C = ∅ := by
  refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun x hxD hxC => ?_)
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  obtain ⟨j, hj⟩ := (hmem x).mp hxD
  exact (deleteFinset_adj.mp (hcyc j)).1 (hj ▸ hxC)

/-- **An odd cycle of `G` avoiding `C` is an odd cycle of the residue** `deleteFinset G C`: the two
adjacency conditions agree on the vertices of the cycle. -/
theorem isOddCycle_of_isOddCycle_avoiding {C D : Finset V} (hD : IsOddCycle G D) (hdis : D ∩ C = ∅) :
    IsOddCycle (deleteFinset G C) D := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hmemD : ∀ j : Fin m, f j ∉ C := by
    intro j
    exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr hdis)
      ((hmem (f j)).mpr ⟨j, rfl⟩))
  refine ⟨m, f, hm, hm3, hinj, fun j => deleteFinset_adj.mpr
    ⟨hmemD j, hmemD (cycSucc j), hcyc j⟩, hmem⟩

/-! ### A packing of the residue, together with the cycle, is a packing of `G` -/

/-- **An odd cycle of the residue is not a member of the family.**  (It is disjoint from `C`, and
`C` is nonempty.) -/
theorem not_mem_of_isOddCycle_delete {C : Finset V} {𝒟 : Finset (Finset V)} {D : Finset V}
    (h𝒟 : IsOddCycleFamily (G := deleteFinset G C) 𝒟) (hC : IsOddCycle G C) (hD : D ∈ 𝒟) :
    C ≠ D := by
  intro hEq
  subst hEq
  have h0 : C ∩ C = ∅ := inter_empty_of_isOddCycle_delete (h𝒟.2 C hD)
  obtain ⟨a, ha⟩ := hC.nonempty
  exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr h0) ha) ha

/-- **A packing of odd cycles of a residue is a packing of odd cycles of `G`.** -/
theorem IsOddCycleFamily.of_deleteFinset {B : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : IsOddCycleFamily (G := deleteFinset G B) 𝒟) : IsOddCycleFamily (G := G) 𝒟 :=
  ⟨h𝒟.1, fun D hD => (h𝒟.2 D hD).of_deleteFinset⟩

/-- **The first step of the Erdős–Pósa induction.**  A packing of odd cycles of the residue
`deleteFinset G C`, together with the odd cycle `C` itself, is a packing of odd cycles of `G`. -/
theorem insert_oddCycle_of_delete {C : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : IsOddCycleFamily (G := deleteFinset G C) 𝒟) (hC : IsOddCycle G C) :
    IsOddCycleFamily (G := G) (insert C 𝒟) := by
  have hfam' : IsOddCycleFamily (G := G) 𝒟 := h𝒟.of_deleteFinset
  refine ⟨?_, ?_⟩
  · intro X hX Y hY hXY
    have hX' : X = C ∨ X ∈ 𝒟 := Finset.mem_insert.mp hX
    have hY' : Y = C ∨ Y ∈ 𝒟 := Finset.mem_insert.mp hY
    rcases hX' with hXC | hXD
    · rcases hY' with hYC | hYD
      · exact absurd (hXC.trans hYC.symm) hXY
      · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun a haX haY => ?_)
        have h0 : Y ∩ C = ∅ := inter_empty_of_isOddCycle_delete (h𝒟.2 Y hYD)
        exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr h0) haY) (hXC ▸ haX)
    · rcases hY' with hYC | hYD
      · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun a haX haY => ?_)
        have h0 : X ∩ C = ∅ := inter_empty_of_isOddCycle_delete (h𝒟.2 X hXD)
        exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr h0) haX) (hYC ▸ haY)
      · exact h𝒟.1 X hXD Y hYD hXY
  · intro X hX
    rcases Finset.mem_insert.mp hX with hXC | hXD
    · exact hXC ▸ hC
    · exact hfam'.2 X hXD

/-- `𝒞` is a **maximum packing** of odd cycles of `G`: a packing of maximum cardinality. -/
def IsMaxOddCyclePacking (G : SimpleGraph V) (𝒞 : Finset (Finset V)) : Prop :=
  IsOddCycleFamily (G := G) 𝒞 ∧ ∀ D, IsOddCycleFamily (G := G) D → D.card ≤ 𝒞.card

/-- A maximum packing of odd cycles exists. -/
theorem exists_maxPacking : ∃ 𝒞 : Finset (Finset V), IsMaxOddCyclePacking G 𝒞 := by
  obtain ⟨𝒞, hfam, hmax⟩ := exists_maxCard_oddCycleFamily (G := G)
  exact ⟨𝒞, hfam, hmax⟩

/-- **The odd cycle packing number of the residue of a packed cycle is smaller by one.**  If `𝒞`
is a maximum packing of `G`, `C ∈ 𝒞` is one of its odd cycles, and `𝒟` is any packing of the
residue `G - C`, then `𝒟` together with `C` is a packing of `G`, so `|𝒟| + 1 ≤ |𝒞|`.

This is the strictly decreasing quantity on which the induction of the classical
Erdős–Pósa proof for odd cycles rests. -/
theorem card_add_one_le_of_mem_maxPacking {𝒞 𝒟 : Finset (Finset V)} {C : Finset V}
    (hmax : IsMaxOddCyclePacking G 𝒞) (hC : IsOddCycle G C) (_hCin : C ∈ 𝒞)
    (h𝒟 : IsOddCycleFamily (G := deleteFinset G C) 𝒟) : 𝒟.card + 1 ≤ 𝒞.card := by
  have hle := hmax.2 (insert C 𝒟) (insert_oddCycle_of_delete h𝒟 hC)
  have hCnotin : C ∉ 𝒟 := fun h => (not_mem_of_isOddCycle_delete h𝒟 hC h) rfl
  rw [Finset.card_insert_of_notMem hCnotin] at hle
  omega

/-- **Erdős's local hypothesis makes the residue bound strict.**  Under `LocIndep k G` at most `k`
vertex-disjoint odd cycles exist, so a packing of the residue of an odd cycle has at most `k - 1`
members. -/
theorem LocIndep.oddCycle_packing_residue_lt {k : ℕ} (hG : LocIndep k G) {C : Finset V}
    (hC : IsOddCycle G C) {𝒟 : Finset (Finset V)}
    (h𝒟 : IsOddCycleFamily (G := deleteFinset G C) 𝒟) : 𝒟.card + 1 ≤ k := by
  have hle := hG.oddCycleFamily_card_le (insert_oddCycle_of_delete h𝒟 hC)
  have hCnotin : C ∉ 𝒟 := fun h => (not_mem_of_isOddCycle_delete h𝒟 hC h) rfl
  rw [Finset.card_insert_of_notMem hCnotin] at hle
  omega

/-- **The residue of a packed cycle only sees the rest of the packing.**  If `𝒞` is a maximum
packing of `G`, `C ∈ 𝒞`, and `D` is an odd cycle avoiding `C`, then `D` meets one of the *other*
members of `𝒞`: a packing of maximum cardinality meets every odd cycle
(`hitsOddCycles_of_maxCardFamily`), and `D` avoids `C`.

This is the cross-intersection statement the classical induction is built on: after deleting one
packed cycle, every odd cycle that is left must go through the remaining `|𝒞| - 1` cycles. -/
theorem residue_hits_rest {𝒞 : Finset (Finset V)} {C D : Finset V}
    (hmax : IsMaxOddCyclePacking G 𝒞) (_hCin : C ∈ 𝒞) (hD : IsOddCycle G D) (hDdis : D ∩ C = ∅) :
    ∃ C' ∈ 𝒞, C' ≠ C ∧ D ∩ C' ≠ ∅ := by
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr
    (hitsOddCycles_of_maxCardFamily hmax.1 hmax.2 D hD)
  obtain ⟨hxD, hxU⟩ := Finset.mem_inter.mp hx
  obtain ⟨C', hC', hxC'⟩ := Finset.mem_biUnion.mp hxU
  refine ⟨C', hC', ?_, ne_inter_of_mem hxD hxC'⟩
  intro hEq
  subst hEq
  exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr hDdis) hxD) hxC'

/-- **A transversal of the residue, together with the cycle, is a transversal of `G`** — the
induction step of the Erdős–Pósa proof for odd cycles. -/
theorem hitsOddCycles_union_cycle {C X : Finset V} (hX : HitsOddCycles (deleteFinset G C) X) :
    HitsOddCycles G (X ∪ C) := by
  intro D hD
  by_cases hDC : D ∩ C = ∅
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hX D (isOddCycle_of_isOddCycle_avoiding hD hDC))
    obtain ⟨hxD, hxX⟩ := Finset.mem_inter.mp hx
    exact ne_inter_of_mem hxD (Finset.mem_union.mpr (Or.inl hxX))
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hDC
    obtain ⟨hxD, hxC⟩ := Finset.mem_inter.mp hx
    exact ne_inter_of_mem hxD (Finset.mem_union.mpr (Or.inr hxC))

/-- **The quantitative induction step.**  If the residue of an odd cycle is `q`-close to bipartite,
then `G` is `q + |C|` close to bipartite.  The classical proof needs `+1` here; the `+|C|` is the
gap recorded in `discovery/JSP-000090/policy.json`. -/
theorem closeToBipartite_of_residue {C : Finset V} {q : ℕ} (h : CloseToBipartite q (deleteFinset G C)) :
    CloseToBipartite (q + C.card) G := by
  obtain ⟨X, hX, hhits⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := deleteFinset G C) (m := q)).mp h
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := q + C.card)).mpr
    ⟨X ∪ C, (Finset.card_union_le _ _).trans (Nat.add_le_add hX (le_refl _)),
      hitsOddCycles_union_cycle hhits⟩

/-! ### The case of packing number one -/

/-- **`G` has odd cycle packing number one**: any two odd cycles of `G` meet. -/
def PackingNumberOne (G : SimpleGraph V) : Prop :=
  ∀ C D : Finset V, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅

/-- **In a graph of packing number one every odd cycle is a transversal, and its residue is
bipartite.**  Indeed an odd cycle of `G` avoiding `C` would be disjoint from `C` (and `C` is
nonempty), contradicting the hypothesis. -/
theorem packing_one_transversal {C : Finset V} (h1 : PackingNumberOne G) (hC : IsOddCycle G C) :
    HitsOddCycles G C ∧ (deleteFinset G C).IsBipartite := by
  refine ⟨?_, ?_⟩
  · intro D hD
    exact h1 D C hD hC
  · exact isBipartite_delete_of_hitsOddCycles (fun D hD => h1 D C hD hC)

/-- **The residue of an odd cycle in a graph of packing number one is bipartite**: every odd cycle
of the residue would be disjoint from `C`. -/
theorem packing_one_residue_bipartite {C : Finset V} (h1 : PackingNumberOne G) (hC : IsOddCycle G C) :
    (deleteFinset G C).IsBipartite := (packing_one_transversal h1 hC).2

/-- **Erdős–Pósa for odd cycles with packing number one, in the form of the conclusion**: if `G`
has an odd cycle `C` of at most `ℓ` vertices and no two of its odd cycles are disjoint, then `G` is
the union of a bipartite graph and `ℓ` vertices. -/
theorem closeToBipartite_of_packing_one {ℓ : ℕ} {C : Finset V}
    (h1 : PackingNumberOne G) (hC : IsOddCycle G C) (hCcard : C.card ≤ ℓ) :
    CloseToBipartite ℓ G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := ℓ)).mpr
    ⟨C, hCcard, (packing_one_transversal h1 hC).1⟩

/-- **A new instance of the headline theorem: graphs of odd cycle packing number one.**  If any
two odd cycles of `G` meet and `G` has an odd cycle, then the shortest one is a transversal, so
`LocIndep k G` forces `CloseToBipartite ℓ G` as soon as `G` has an odd cycle of at most `ℓ`
vertices — with a constant `ℓ` that does **not** grow with `k` (the bounded-odd-girth instance
`erdos73On_of_bounded_odd_girth` only gives `ℓ * k`), and with no assumption on branch vertices
(so the branch-vertex instances of round 38 do not apply: `K_5` has packing number one and is full
of branch vertices). -/
theorem erdos73On_of_packing_one (k ℓ : ℕ) :
    ∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → PackingNumberOne G →
      (∃ C, IsOddCycle G C ∧ C.card ≤ ℓ) → CloseToBipartite ℓ G := by
  intro W instW G _hG h1 ⟨C, hC, hCcard⟩
  exact closeToBipartite_of_packing_one (ℓ := ℓ) h1 hC hCcard

/-- **The complementary case of the same instance:** a graph of packing number one with no odd
cycle at all is bipartite and needs no modifications. -/
theorem closeToBipartite_of_packing_one_no_oddCycle (_h1 : PackingNumberOne G)
    (hno : ¬ ∃ C : Finset V, IsOddCycle G C) : CloseToBipartite 0 G :=
  isBipartite_closeToBipartite (m := 0) (isBipartite_of_no_oddCycle (G := G) hno)

/-! ### Minimum and minimal odd cycle transversals -/

/-- A vertex different from `x` is not a member of the singleton `{x}`. -/
theorem not_mem_singleton_of_ne {x y : V} (h : y ≠ x) : y ∉ ({x} : Finset V) := by
  rw [Finset.mem_singleton]
  exact h

/-- `X` is a **minimal** odd cycle transversal of `G`: it meets every odd cycle, and no vertex can
be deleted from it. -/
def IsMinimalTransversal (G : SimpleGraph V) (X : Finset V) : Prop :=
  HitsOddCycles G X ∧ ∀ x ∈ X, ¬ HitsOddCycles G (X \ {x})

/-- **A minimal transversal exists inside any given transversal.**  Among the transversals
contained in `X₀`, one of least cardinality is minimal, since `X \ {x}` is again contained in `X₀`
and is a proper part of `X` whenever `x ∈ X`.

This is the object the classical proof of Erdős–Pósa for odd cycles manipulates: a transversal
whose every vertex is needed. -/
theorem exists_minimalTransversal_of_transversal (X₀ : Finset V) (hX₀ : HitsOddCycles G X₀) :
    ∃ X : Finset V, X ⊆ X₀ ∧ IsMinimalTransversal G X := by
  classical
  have hsne : ((Finset.univ : Finset (Finset V)).filter
      (fun Y : Finset V => Y ⊆ X₀ ∧ HitsOddCycles G Y)).Nonempty := by
    refine Finset.filter_nonempty_iff.mpr
      ⟨X₀, Finset.mem_univ _, Finset.Subset.refl _, hX₀⟩
  obtain ⟨X, hXs, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset V)).filter
      (fun Y : Finset V => Y ⊆ X₀ ∧ HitsOddCycles G Y)) Finset.card hsne
  have hXs' := hXs
  rw [Finset.mem_filter] at hXs'
  obtain ⟨hXsub, hX⟩ := hXs'.2
  refine ⟨X, hXsub, hX, fun x hx hX' => ?_⟩
  have hmem : (X \ {x} : Finset V)
      ∈ (Finset.univ : Finset (Finset V)).filter
          (fun Y : Finset V => Y ⊆ X₀ ∧ HitsOddCycles G Y) := by
    have hsub2 : X \ {x} ⊆ X₀ := fun a ha => hXsub (Finset.mem_sdiff.mp ha).1
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsub2, hX'⟩
  have hcard : (X \ {x}).card + 1 = X.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hx)
    simpa using h
  have hlt : (X \ {x}).card < X.card := by omega
  exact absurd hlt (Nat.not_lt.mpr (hmin (X \ {x}) hmem))

/-- **A minimal transversal exists.**  The empty set is a transversal whenever `G` is bipartite;
otherwise the union of all odd cycles of `G` is one (every odd cycle meets itself), and
`exists_minimalTransversal_of_transversal` applies to it. -/
theorem exists_minimalTransversal : ∃ X : Finset V, IsMinimalTransversal G X := by
  classical
  by_cases hb : G.IsBipartite
  · refine ⟨∅, hitsOddCycles_of_isBipartite_delete (isBipartite_delete (X := ∅) hb), fun x hx => ?_⟩
    exact absurd hx (by simp)
  · obtain ⟨D, hD⟩ : ∃ D : Finset V, IsOddCycle G D := by
      by_contra hcon
      exact hb (isBipartite_of_no_oddCycle (G := G) hcon)
    have hU : HitsOddCycles G (((Finset.univ : Finset (Finset V)).filter (IsOddCycle G)).biUnion id) := by
      intro C hC
      obtain ⟨x, hx⟩ := hC.nonempty
      have hmemC : C ∈ (Finset.univ : Finset (Finset V)).filter (IsOddCycle G) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hC⟩
      exact ne_inter_of_mem hx (Finset.mem_biUnion.mpr ⟨C, hmemC, hx⟩)
    obtain ⟨X, -, hX⟩ := exists_minimalTransversal_of_transversal _ hU
    exact ⟨X, hX⟩

/-- **A minimal transversal of at most `m` vertices witnesses that `G` is `m`-close to
bipartite** — i.e. the odd cycle transversal number is attained by a minimal transversal, which is
how the classical argument starts. -/
theorem closeToBipartite_of_minimalTransversal (X : Finset V) (hX : IsMinimalTransversal G X) :
    CloseToBipartite X.card G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := X.card)).mpr ⟨X, le_refl _, hX.1⟩

/-- **Every vertex of a minimal transversal lies alone on an odd cycle.**  If every odd cycle met
`X` in at least two vertices, then `X \ {x}` would still be a transversal.  These "private" odd
cycles are the objects the absorption step of the classical Erdős–Pósa proof has to charge against
a maximum packing. -/
theorem exists_private_oddCycle {X : Finset V} (hX : IsMinimalTransversal G X) {x : V} (hx : x ∈ X) :
    ∃ D : Finset V, IsOddCycle G D ∧ D ∩ X = {x} := by
  classical
  obtain ⟨D, hD, hDdis⟩ : ∃ D : Finset V, IsOddCycle G D ∧ D ∩ (X \ {x}) = ∅ := by
    by_contra hcon
    refine hX.2 x hx fun D hD hne => hcon ⟨D, hD, ?_⟩
    refine Finset.eq_empty_iff_forall_notMem.mpr fun a ha => ?_
    exact absurd ha (by rw [hne]; simp)
  have hcontra : ∀ y : V, ¬ (y ∈ D ∧ y ∈ X \ {x}) := by
    intro y hy
    have hmem : y ∈ D ∩ (X \ {x}) := Finset.mem_inter.mpr ⟨hy.1, hy.2⟩
    rw [hDdis] at hmem
    simp at hmem
  -- the private odd cycle is nonempty and meets `X`, so its only vertex in `X` is `x`
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (hX.1 D hD)
  have hw' : w ∈ D ∧ w ∈ X := Finset.mem_inter.mp hw
  have hwx : w = x := by
    by_cases hweq : w = x
    · exact hweq
    · exfalso
      have hmem : w ∈ X \ {x} := Finset.mem_sdiff.mpr ⟨hw'.right, not_mem_singleton_of_ne hweq⟩
      exact hcontra w ⟨hw'.left, hmem⟩
  have hxD : x ∈ D := hwx ▸ hw'.left
  refine ⟨D, hD, Finset.Subset.antisymm (fun (y : V) (hy : y ∈ D ∩ X) => ?_) (fun (y : V) => ?_)⟩
  · by_cases hyx : y = x
    · exact Finset.mem_singleton.mpr hyx
    · exfalso
      have hy' : y ∈ D ∧ y ∈ X := Finset.mem_inter.mp hy
      have hmem : y ∈ X \ {x} := Finset.mem_sdiff.mpr ⟨hy'.right, not_mem_singleton_of_ne hyx⟩
      exact hcontra y ⟨hy'.left, hmem⟩
  · intro hy
    have hyx : y = x := Finset.mem_singleton.mp hy
    rw [hyx]
    exact Finset.mem_inter.mpr ⟨hxD, hx⟩

/-- **Pairwise disjoint private odd cycles of a minimal transversal are a packing, so under Erdős's
local hypothesis there are at most `k` of them.**  This is the quantitative form of the
observation that the absorption step must charge every vertex of a minimum transversal against a
different member of a maximum packing. -/
theorem card_le_of_disjoint_private_cycles {k : ℕ} (hG : LocIndep k G) {X : Finset V}
    (_hX : IsMinimalTransversal G X) (D : ↥X → Finset V) (hDcyc : ∀ x : ↥X, IsOddCycle G (D x))
    (hDdis : ∀ x y : ↥X, x ≠ y → D x ∩ D y = ∅) : X.card ≤ k := by
  classical
  have hne : ∀ x : ↥X, (D x).Nonempty := fun x => (hDcyc x).nonempty
  set fam : Finset (Finset V) := X.attach.image (fun x : ↥X => D x) with hfam
  have hcard : fam.card = X.card := by
    rw [hfam, Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro a b hab
      by_cases hne' : a = b
      · exact hne'
      · obtain ⟨z, hz⟩ := hne a
        have hne1 : Finset.Nonempty (D a ∩ D a) :=
          ⟨z, Finset.mem_inter.mpr ⟨hz, hz⟩⟩
        have hEq : D a ∩ D a = D a ∩ D b := congrArg (fun t : Finset V => D a ∩ t) hab
        have hneab : Finset.Nonempty (D a ∩ D b) := hEq ▸ hne1
        have hdis : Disjoint (D a) (D b) := by
          rw [Finset.disjoint_iff_inter_eq_empty, hDdis a b hne']
        obtain ⟨w, hw⟩ := hneab
        have hw' : w ∈ D a ∧ w ∈ D b := Finset.mem_inter.mp hw
        exact absurd hw'.right (Finset.disjoint_left.mp hdis hw'.left)
  have hfam' : IsOddCycleFamily (G := G) fam := by
    refine ⟨?_, ?_⟩
    · intro Y hY Z hZ hYZ
      obtain ⟨a, ha, hYa⟩ := Finset.mem_image.mp hY
      obtain ⟨b, hb, hZb⟩ := Finset.mem_image.mp hZ
      by_cases hne' : a = b
      · exfalso
        have hYZ' : Y = Z := hYa.symm.trans ((congrArg D hne').trans hZb)
        exact hYZ hYZ'
      · have hEq : D a ∩ D b = Y ∩ Z := congrArg₂ (fun s t : Finset V => s ∩ t) hYa hZb
        rw [← hEq]
        exact hDdis a b hne'
    · intro Y hY
      obtain ⟨a, ha, hYa⟩ := Finset.mem_image.mp hY
      exact hYa ▸ hDcyc a
  have hle := hG.oddCycleFamily_card_le hfam'
  rw [hcard] at hle
  exact hle

end

end JSP90
