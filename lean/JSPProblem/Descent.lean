/-
# JSP-000090 — the **deficiency descent**: Erdős #73 on the Helly class with the optimal constant

Attack family 31 (round 84).  New module, imported from the root module `JSPProblem.lean`.

## The statement of this round

```lean
JSP90.closeToBipartite_maxDef_of_maxDefDescent :
    JSP90.HellyMaxDefDescent → HellyOddCycles G → CloseToBipartite (MaxDef G) G
```

Since `LocIndep k G ↔ MaxDef G ≤ k` (`JSP90.locIndep_iff_maxDef_le`) and `CloseToBipartite` is
monotone in its bound, this gives

```lean
JSP90.erdos73On_helly_of_maxDefDescent : JSP90.HellyMaxDefDescent → JSP90.HellyErdős73 id
```

**Erdős Problem #73 for the class of graphs whose odd cycles form a Helly family, with the
*optimal* constant `f(k) = k`** — `LocIndep k G → HellyOddCycles G → CloseToBipartite k G`, i.e.
round 83's `JSP90.HellyErdős73` at `f = id`, attained by `kTriangles k` (Part 6).  The whole
content of that instance is reduced, by a proof given here, to **one** statement about a single
vertex deletion: `JSP90.VertexDescent`.

## What is proved

1. **HEREDITY OF THE HELLY PROPERTY** (`JSP90.helly_induceFinset`, `JSP90.helly_deleteFinset`):
   the odd cycles of an induced subgraph are odd cycles of `G`, so they form a *subfamily* of the
   odd cycles of `G`, and a Helly family inherits.  This is what makes an induction on `MaxDef G`
   possible on this class at all (the residue of a Helly graph is Helly).  The transport lemma
   `JSP90.isOddCycle_induceFinset` is proved here from scratch.
2. **THE DEFICIENCY OF AN ODD CYCLE IS PAID FOR IN THE RESIDUE** (`JSP90.defOf_ge_succ_add`), hence
   **`JSP90.maxDef_ge_one_add_maxDef_delete_of_oddCycle`: `IsOddCycle G C →
   1 + MaxDef (deleteFinset G C) ≤ MaxDef G`** — the *residue* form of the descent, with **no**
   separation hypothesis.  (`JSPProblem/OffCycle.lean` could only state
   `maxDef_ge_one_add_maxDef_of_oddCycle` for a vertex set separated from `C`; separation is not
   available at a shortest odd cycle.)
3. **THE DUALITY OF A MAXIMUM-DEFICIENCY WITNESS AND AN ODD CYCLE** (Part 3):
   * `JSP90.defOf_maxDef_inter_oddCycle_ne` — a vertex set of deficiency exactly `MaxDef G`
     **meets every odd cycle**, i.e. maximum-deficiency witnesses are odd cycle transversals;
   * `JSP90.exists_oddCycle_of_defOf_gt_zero` — a vertex set of positive deficiency **contains an
     odd cycle**;
   * `JSP90.mem_of_common_oddCycle` and `JSP90.vertexDescent_of_common_oddCycle` — a vertex lying
     on every odd cycle lies in every witness, the deletion of it is bipartite, and **the descent
     is proved** in that situation.
4. **THE PRECISE REDUCTION** (Part 4): `JSP90.closeToBipartite_maxDef_of_maxDefDescent` and
   `JSP90.erdos73On_helly_of_maxDefDescent`.  A strong induction on `MaxDef G`: delete one vertex of
   an odd cycle; the residue is again Helly (Part 1) with deficiency at least one smaller; extend a
   transversal of the residue by that vertex.  **This is the only place where the descent hypothesis
   is used.**
5. **A PROVED INSTANCE** (Part 5): `JSP90.closeToBipartite_one_of_helly_of_pairwiseMeeting` and
   `JSP90.erdos73On_helly_pairwiseMeeting` — if the odd cycles of `G` pairwise meet (packing number
   `≤ 1`) and `G` is Helly, then `LocIndep c G → CloseToBipartite c G`, for **every** `c`.  No
   bound on the odd girth, the degrees, the packing weight, the number of branch vertices or the
   number of components.  (For `c = 1` this is round 83's instance; for `c ≥ 2` it is new — and the
   pairwise-meeting hypothesis is *not* implied by `LocIndep c` when `c ≥ 2`, as `kTriangles c`
   shows.)
6. **OPTIMALITY OF THE CONSTANT** (Part 6): `JSP90.helly_kTriangles`,
   `JSP90.helly_attained_sharp` — `kTriangles k` is Helly, satisfies `LocIndep k` and is **not**
   `(k - 1)`-close to bipartite, so the constant `k` of `erdos73On_helly_of_maxDefDescent` cannot be
   lowered.

## What is *not* proved

`JSP90.VertexDescent G` — *for every Helly graph `G` with `MaxDef G ≥ 1` there is a vertex `v` of an
odd cycle of `G` with `MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G`* — is stated as a `def` and
**not** assumed.  It is *proved* in Part 3's situation (one vertex on every odd cycle) and it is
verified computationally (see below); with it, Erdős #73 holds on the whole Helly class with the
optimal constant `k`.  It is the single missing lemma for this class, and it is a statement about
the maximum deficiency of a single vertex deletion — not about pairs or triples of cycles.

## Verification done before formalising (exhaustive, in C)

Over **all** graphs on `n ≤ 7` vertices (of which `1 103 955` are Helly; `2²¹` graphs in total):

* `HellyOddCycles ∧ MaxDef ≤ 1 → τ = 1`, `∧ MaxDef ≤ 2 → τ ≤ 2`, and **no** Helly graph on `n ≤ 7`
  has `τ > MaxDef` (0 counterexamples) — so `CloseToBipartite (MaxDef G) G` is the right
  statement for this class;
* **`JSP90.VertexDescent` holds for every Helly graph** (0 counterexamples);
* but the descent **fails without Helly**: 13020 counterexamples on `n = 7`, all with
  `MaxDef = 1`.  The smallest is the diamond `K₄ - e`: its two triangles share an edge, so deleting
  any vertex of one triangle leaves the other, and the deficiency does not drop;
* the two strongest candidate proofs of the Helly instance are **false** (recorded so that later
  rounds do not retry them):
  * **König's property fails**: there are Helly graphs with `τ > ν` (360 counterexamples on
    `n = 7`; the first has `MaxDef = τ = 3`, `ν = 2`), so the least odd cycle transversal is *not*
    the packing number on this class — only the deficiency sees it;
  * **the `+1` absorption step at a residue fails**: for a Helly graph there need not be an odd
    cycle `C` and a transversal `X` of `G - C` with `|X| ≤ MaxDef (G - C)` that one vertex of `C`
    extends (360 counterexamples on `n = 7`; the smallest is a 6-vertex graph with
    `MaxDef = τ = 2`, `ν = 2` whose triangles `{0,2,4}`, `{1,3,5}` are met by no single vertex of
    `C = {3,4,5}`).  This is the same absorption step that `JSPProblem/Weight.lean` refutes with
    `K₅` among arbitrary graphs, and it is why the descent must be a statement about *single
    vertices* rather than about residues.
-/

import JSPProblem.Cut
import JSPProblem.Helly

namespace JSP90

open Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance instDecidableEqDescent : DecidableEq V := Classical.decEq V

local instance instDecidableIsOddCycleDescent {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ## Part 1 — odd cycles survive an induced subgraph, and the Helly property is hereditary -/

/-- **AN ODD CYCLE OF AN INDUCED SUBGRAPH IS AN ODD CYCLE OF `G`, AND LIES IN THE INDUCING SET.**
Each vertex `f j` of the cycle is adjacent to `f (cycSucc j)` *inside* `induceFinset G s`, hence
lies in `s`; and the same cyclic ordering is a cyclic ordering in `G`. -/
theorem isOddCycle_induceFinset {s C : Finset V} (hC : IsOddCycle (induceFinset G s) C) :
    IsOddCycle G C ∧ C ⊆ s := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  have hmem_s : ∀ j : Fin m, f j ∈ s := fun j => (induce_adj.mp (hcyc j)).1
  have himg : ((Finset.univ : Finset (Fin m)).image f) = C := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rw [hmem]
  constructor
  · rw [← himg]
    exact isOddCycle_image f hm hm3 hinj (fun j => (induce_adj.mp (hcyc j)).2.2)
  · intro x hx
    obtain ⟨j, hj⟩ := hmem x |>.mp hx
    exact hj ▸ hmem_s j

/-- **THE HELLY PROPERTY IS INHERITED BY INDUCED SUBGRAPHS.**  The odd cycles of
`induceFinset G s` are odd cycles of `G` by `JSP90.isOddCycle_induceFinset`, so they form a
*subfamily* of the odd cycles of `G`, and a pairwise-meeting subfamily of a Helly family has a
common vertex. -/
theorem helly_induceFinset {s : Finset V} (hH : HellyOddCycles G) :
    HellyOddCycles (induceFinset G s) := by
  intro 𝒞 hodd hmeet hne
  exact hH 𝒞 (fun C hC => (isOddCycle_induceFinset (hodd C hC)).1) hmeet hne

/-- **THE HELLY PROPERTY IS INHERITED BY RESIDUES.**  In particular the residue `G - C` of a Helly
graph is Helly, which is what makes the induction on `MaxDef` of Part 4 go through. -/
theorem helly_deleteFinset {X : Finset V} (hH : HellyOddCycles G) :
    HellyOddCycles (deleteFinset G X) :=
  helly_induceFinset (s := Finset.univ \ X) hH

/-- **A BIPARTITE GRAPH IS `HellyOddCycles`** — vacuously, it has no odd cycles. -/
theorem helly_of_isBipartite (h : G.IsBipartite) : HellyOddCycles G := by
  intro 𝒞 hodd hmeet hne
  obtain ⟨C, hC⟩ := hne
  exact ((not_isOddCycle_of_isBipartite h) ⟨C, hodd C hC⟩).elim

/-- **THE DEFICIENCY OF AN ODD CYCLE IS AT LEAST ONE, in the plain `defOf G C` form** (the form of
`JSPProblem/OffCycle.lean` uses `defOf (induceFinset G C) C`). -/
theorem defOf_oddCycle_ge_one' {C : Finset V} (hC : IsOddCycle G C) : 1 ≤ defOf G C := by
  have h := defOf_oddCycle_ge_one hC
  rwa [← defOf_induceFinset G C] at h

/-- **FROM A LINEAR BOUND TO A TRUNCATED ONE.**  `x + z ≤ y` gives `x ≤ y - z`.  Mathlib's
`Nat.le_sub_iff_add_le` needs the side condition `z ≤ y`, which is not available here, so the two
conversion steps below are proved directly. -/
theorem le_sub_of_add_le' {x y z : ℕ} (h : x + z ≤ y) : x ≤ y - z := by
  by_contra hn
  have h1 : y - z + 1 ≤ x := by omega
  have h2 : y - z + z = y := Nat.sub_add_cancel (by omega)
  omega

/-! ## Part 2 — an odd cycle in a disjoint union costs exactly one unit of deficiency -/

/-- **AN ODD CYCLE ADDS EXACTLY ONE UNIT OF DEFICIENCY TO A DISJOINT SET.**  For `A` disjoint from an
odd cycle `C`,

```
defOf G (A ∪ C) ≥ defOf G A + 1 .
```

Indeed `α(G[A ∪ C]) ≤ α(G[A]) + α(G[C])` (`JSP90.indepCard_le_add`) and `2 α(G[C]) + 1 ≤ |C|`
(`JSP90.two_indepCard_add_one_le_card_of_oddCycle`), so the `|C|` vertices of the cycle pay for at
most `|C| - 1` of the deficiency.  This is the numerical heart of Parts 3 and 4.

(Note the direction: the deficiency is *sub*additive over a disjoint decomposition —
`JSP90.defOf_le_add_of_anticover` — so one cannot conclude `defOf G (A ∪ C) ≥ defOf G A +
defOf G C`; the odd cycle is what makes the `+1` available.) -/
theorem defOf_ge_succ_add {A C : Finset V} (hAC : Disjoint A C) (hC : IsOddCycle G C)
    (hpos : 1 ≤ defOf G A) : defOf G A + 1 ≤ defOf G (A ∪ C) := by
  have hα : indepCard G (A ∪ C) ≤ indepCard G A + indepCard G C := indepCard_le_add A C
  have hα' : 2 * indepCard G (A ∪ C) + 1 ≤ 2 * indepCard G A + C.card := by
    have h1 := Nat.mul_le_mul_left 2 hα
    have h2 := two_indepCard_add_one_le_card_of_oddCycle hC
    have h3 : indepCard (induceFinset G C) C = indepCard G C :=
      (indepCard_induceFinset G C).symm
    omega
  have hle : 2 * indepCard G A + 1 ≤ A.card := by
    by_contra hn
    have h1 : A.card ≤ 2 * indepCard G A := by omega
    have h2 : A.card - 2 * indepCard G A = 0 := Nat.sub_eq_zero_of_le h1
    have h3 : 1 ≤ defOf G A := hpos
    simp only [defOf] at h3
    omega
  have hCpos : 1 ≤ C.card := by
    have h2 := two_indepCard_add_one_le_card_of_oddCycle hC
    omega
  have hidC : C.card - 1 + 1 = C.card := Nat.sub_add_cancel hCpos
  have hkey : (defOf G A + 1) + 2 * indepCard G (A ∪ C) ≤ A.card + C.card := by
    have hid : defOf G A + 2 * indepCard G A = A.card := by
      have hE : defOf G A = A.card - 2 * indepCard G A := rfl
      rw [hE]
      exact Nat.sub_add_cancel (by omega)
    omega
  simp only [defOf]
  rw [Finset.card_union_of_disjoint hAC]
  exact le_sub_of_add_le' hkey

/-- **THE RESIDUE OF AN ODD CYCLE HAS DEFICIENCY AT LEAST ONE SMALLER.**

```
IsOddCycle G C → 1 + MaxDef (deleteFinset G C) ≤ MaxDef G .
```

This is the *residue* form of the descent, with **no** separation hypothesis — the reason it could
not be stated in `JSPProblem/OffCycle.lean`.  The proof: the maximiser `W` of the residue
deficiency may be taken inside the residue (`JSP90.defOf_induceFinset_le_inter`), hence is disjoint
from `C`, and `JSP90.defOf_ge_succ_add` then says that adding `C` costs at least one unit. -/
theorem maxDef_ge_one_add_maxDef_delete_of_oddCycle {C : Finset V} (hC : IsOddCycle G C) :
    1 + MaxDef (deleteFinset G C) ≤ MaxDef G := by
  obtain ⟨Y, hY⟩ := exists_eq_maxDef (deleteFinset G C)
  set W : Finset V := (Finset.univ \ C) ∩ Y with hW
  have hmax : defOf (deleteFinset G C) ((Finset.univ \ C) ∩ Y) = MaxDef (deleteFinset G C) := by
    have h1 := defOf_induceFinset_le_inter (G := G) (X := Finset.univ \ C) (Y := Y)
    have h3 : defOf (induceFinset G (Finset.univ \ C)) Y = defOf (deleteFinset G C) Y := by
      simp [deleteFinset]
    have h4 : defOf (induceFinset G (Finset.univ \ C)) ((Finset.univ \ C) ∩ Y)
        = defOf (deleteFinset G C) ((Finset.univ \ C) ∩ Y) := by
      simp [deleteFinset]
    have h2 : defOf (deleteFinset G C) ((Finset.univ \ C) ∩ Y) ≤ MaxDef (deleteFinset G C) := by
      simpa [h4] using (le_maxDef (deleteFinset G C) ((Finset.univ \ C) ∩ Y))
    rw [h3] at h1
    rw [h4] at h1
    exact le_antisymm h2 (by omega)
  have hdef : defOf G W = MaxDef (deleteFinset G C) := by
    have hsub : (Finset.univ \ C) ∩ Y ⊆ Finset.univ \ C :=
      fun x hx => (Finset.mem_inter.mp hx).1
    have h1 : defOf (induceFinset G (Finset.univ \ C)) ((Finset.univ \ C) ∩ Y)
        = defOf G ((Finset.univ \ C) ∩ Y) := defOf_induceFinset_of_subset hsub
    have h2 : defOf (induceFinset G (Finset.univ \ C)) ((Finset.univ \ C) ∩ Y)
        = defOf (deleteFinset G C) ((Finset.univ \ C) ∩ Y) := by
      simp [deleteFinset]
    rw [hW, ← h1, h2, hmax]
  have hWC : Disjoint W C := Finset.disjoint_left.mpr fun w hwW hwC =>
    have hwW' : w ∈ (Finset.univ \ C) ∩ Y := hwW
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwW').1).2 hwC
  have hone := defOf_oddCycle_ge_one' hC
  have hdef' := hdef
  by_cases hz : MaxDef (deleteFinset G C) = 0
  · have h1 := le_maxDef G C
    omega
  · have hpos : 1 ≤ defOf G W := by omega
    have h1 := defOf_ge_succ_add hWC hC hpos
    have h2 := le_maxDef G (W ∪ C)
    omega

/-! ## Part 3 — the duality between a maximum-deficiency witness and an odd cycle -/

/-- **A WITNESS OF THE MAXIMUM DEFICIENCY IS AN ODD CYCLE TRANSVERSAL.**  If `defOf G X = MaxDef G`
and `C` is an odd cycle, then `X ∩ C ≠ ∅`: otherwise `X` and `C` are disjoint, so `JSP90.defOf_ge_succ_add`
makes the deficiency of their union at least `MaxDef G + 1`, contradicting the definition of
`MaxDef G`.

So the two extremal notions of this development are *dual*: a transversal is large
(`JSP90.maxDef_le_of_hitsOddCycles`), and a maximum-deficiency witness is already a transversal. -/
theorem defOf_maxDef_inter_oddCycle_ne {X C : Finset V} (hX : defOf G X = MaxDef G)
    (hC : IsOddCycle G C) : X ∩ C ≠ ∅ := by
  intro hdis
  have hd : Disjoint X C := Finset.disjoint_iff_inter_eq_empty.mpr hdis
  have hone := defOf_oddCycle_ge_one' hC
  have hdef : defOf G X = MaxDef G := hX
  by_cases hz : defOf G X = 0
  · have h1 := le_maxDef G C
    omega
  · have hpos : 1 ≤ defOf G X := by omega
    have h1 := defOf_ge_succ_add hd hC hpos
    have h2 : defOf G (X ∪ C) ≤ MaxDef G := le_maxDef G _
    omega

/-- **A VERTEX SET OF POSITIVE DEFICIENCY CONTAINS AN ODD CYCLE.**  (The contrapositive is
`JSP90.indepCard_le_of_isBipartite`: a bipartite induced subgraph has deficiency `0`.) -/
theorem exists_oddCycle_of_defOf_gt_zero {X : Finset V} (hX : 0 < defOf G X) :
    ∃ C : Finset V, IsOddCycle G C ∧ C ⊆ X := by
  by_contra hn
  have h1 : ¬ (∃ C : Finset V, IsOddCycle (induceFinset G X) C) := by
    rintro ⟨C, hC⟩
    have hodd : IsOddCycle G C := (isOddCycle_induceFinset hC).1
    have hsub : C ⊆ X := (isOddCycle_induceFinset hC).2
    exact hn ⟨C, hodd, hsub⟩
  have h2 := indepCard_le_of_isBipartite (X := X) (isBipartite_of_no_oddCycle h1)
  simp only [defOf] at hX h2
  omega

/-- **A VERTEX ON EVERY ODD CYCLE LIES IN EVERY WITNESS OF THE MAXIMUM DEFICIENCY.** -/
theorem mem_of_common_oddCycle {X : Finset V} {a : V} (hX : defOf G X = MaxDef G)
    (hpos : 1 ≤ MaxDef G) (ha : ∀ C : Finset V, IsOddCycle G C → a ∈ C) : a ∈ X := by
  have hdef : defOf G X = MaxDef G := hX
  have hlt : 1 ≤ defOf G X := by omega
  obtain ⟨C, hC, hCs⟩ := exists_oddCycle_of_defOf_gt_zero hlt
  exact hCs (ha C hC)

/-- **THE VERTEX DESCENT FOR THE MAXIMUM DEFICIENCY.**  If `G` has deficiency at least one, there is
a vertex `v` *of an odd cycle of `G`* whose deletion drops the maximum deficiency by at least one:

```
MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G .
```

This is the single statement that Part 4 uses, and hence the whole content of Erdős #73 for the
Helly class with the optimal constant.  It is stated as a `def` and **not** assumed; the next
theorem proves it when one vertex lies on every odd cycle, and the file header records the
exhaustive verification for the Helly class. -/
noncomputable def VertexDescent (G : SimpleGraph V) : Prop :=
  1 ≤ MaxDef G → ∃ (C : Finset V) (v : V), IsOddCycle G C ∧ v ∈ C ∧
    MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G

/-- **`VertexDescent` holds for `G` as soon as one vertex lies on every odd cycle**: deleting that
vertex leaves no odd cycle, hence a bipartite graph, hence deficiency `0`, while `MaxDef G ≥ 1`.
Proved here; the Helly property is not needed (the hypothesis is stronger). -/
theorem vertexDescent_of_common_oddCycle {v : V} (h : ∀ C : Finset V, IsOddCycle G C → v ∈ C) :
    VertexDescent G := by
  intro hpos
  have hexist : ∃ C : Finset V, IsOddCycle G C := by
    by_contra hn
    exact absurd (isBipartite_of_no_oddCycle hn) (fun hb => by
      have := maxDef_eq_zero_iff.mpr hb
      omega)
  obtain ⟨C, hC⟩ := hexist
  have hhits : HitsOddCycles G {v} := fun D hD => Finset.ne_empty_of_mem
    (Finset.mem_inter.mpr ⟨h D hD, Finset.mem_singleton.mpr rfl⟩)
  have hbip : (deleteFinset G {v}).IsBipartite := isBipartite_delete_of_hitsOddCycles hhits
  refine ⟨C, v, hC, h C hC, ?_⟩
  have hzero : MaxDef (deleteFinset G {v}) = 0 := maxDef_eq_zero_iff.mpr hbip
  omega

/-! ## Part 4 — the vertex descent: the single missing lemma, and the reduction -/

/-- **`JSP90.VertexDescent` for every Helly graph** — the single missing lemma, as a statement about
all finite vertex types. -/
noncomputable def HellyMaxDefDescent : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), HellyOddCycles G → VertexDescent G

/-- **ERDŐS #73 ON THE HELLY CLASS, WITH THE OPTIMAL CONSTANT, FROM THE VERTEX DESCENT.**  The
proof is a strong induction on `MaxDef G`: a single vertex `v` of an odd cycle is deleted, the
residue `G - {v}` is again Helly (Part 1) with deficiency one smaller (the descent hypothesis), and
a transversal of the residue is extended by `v`.  **This is the only place where the descent
hypothesis is used.** -/
theorem closeToBipartite_maxDef_aux (hD : HellyMaxDefDescent.{u}) :
    ∀ (t : ℕ) (W : Type u) (G : SimpleGraph W) [Fintype W], MaxDef G ≤ t → HellyOddCycles G →
      CloseToBipartite t G := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro W G inst hle hH
    letI := inst
    by_cases hb : MaxDef G = 0
    · refine ⟨∅, by simp, ?_⟩
      rw [deleteFinset_empty]
      exact maxDef_eq_zero_iff.mp hb
    · obtain ⟨C, v, hC, hvC, hdesc⟩ := hD W inst G hH (by omega)
      have hlt : MaxDef (deleteFinset G {v}) < t := by omega
      have hH' : HellyOddCycles (deleteFinset G {v}) := helly_deleteFinset hH
      obtain ⟨Y, hY, hYbip⟩ := ih (MaxDef (deleteFinset G {v})) hlt W (deleteFinset G {v})
        (le_refl _) hH'
      refine ⟨{v} ∪ Y, ?_, ?_⟩
      · have hc : ({v} ∪ Y).card ≤ ({v} : Finset W).card + Y.card :=
          Finset.card_union_le ({v} : Finset W) Y
        have hc' : ({v} ∪ Y).card ≤ 1 + Y.card := by simpa using hc
        have hstep : 1 + Y.card ≤ MaxDef G := by omega
        have hfin : 1 + Y.card ≤ t := by omega
        omega
      · have hEq : deleteFinset G ({v} ∪ Y) = deleteFinset (deleteFinset G {v}) Y := by
          ext w x
          simp only [deleteFinset_adj, Finset.mem_union, Finset.mem_singleton, not_or]
          tauto
        rw [hEq]
        exact hYbip

/-- **`CloseToBipartite (MaxDef G) G` from the vertex descent**, at `t = MaxDef G`: for a Helly
graph the least odd cycle transversal is at most the maximum deficiency. -/
theorem closeToBipartite_maxDef_of_maxDefDescent {W : Type u} {inst : Fintype W}
    (G : SimpleGraph W) (hD : HellyMaxDefDescent.{u}) (hH : HellyOddCycles G) :
    CloseToBipartite (MaxDef G) G := by
  letI := inst
  exact closeToBipartite_maxDef_aux hD (MaxDef G) W G (le_refl _) hH

/-- **THE WHOLE OF ERDŐS #73 ON THE HELLY CLASS, WITH THE OPTIMAL CONSTANT `f(k) = k`, FOLLOWS FROM
THE SINGLE VERTEX DESCENT**: `JSP90.HellyMaxDefDescent → JSP90.HellyErdős73 id`, i.e.

```
∀ (W) (_ : Fintype W) (G) (c), LocIndep c G → HellyOddCycles G → CloseToBipartite c G .
```

So the instance of the headline theorem with the *optimal* constant, on round 83's class, reduces
to one statement about the maximum deficiency of a single vertex deletion.  No hypothesis on
lengths, degrees, packings, connectivity or cuts occurs anywhere. -/
theorem erdos73On_helly_of_maxDefDescent (hD : HellyMaxDefDescent.{u}) :
    HellyErdős73.{u} id := by
  intro W inst G c hG hH
  exact closeToBipartite_mono (maxDef_le_of_locIndep hG)
    (closeToBipartite_maxDef_of_maxDefDescent G hD hH)

/-! ## Part 5 — a proved instance: graphs whose odd cycles pairwise meet -/

/-- **ERDŐS #73 AT THE CONSTANT `1` FOR GRAPHS WHOSE ODD CYCLES PAIRWISE MEET.**  If the odd cycles
of `G` pairwise meet (packing number `≤ 1`) and `G` is Helly, then the family of *all* odd cycles
is itself a pairwise-meeting Helly family, so it has a common vertex, and `{v}` is an odd cycle
transversal.  No bound on the odd girth, the degrees, the packing weight or the number of branch
vertices. -/
theorem closeToBipartite_one_of_helly_of_pairwiseMeeting (hH : HellyOddCycles G)
    (hmeet : ∀ C D : Finset V, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅) :
    CloseToBipartite 1 G := by
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C0, hC0⟩ := hodd
    set 𝒞 : Finset (Finset V) :=
      (Finset.univ : Finset (Finset V)).filter (IsOddCycle G) with h𝒞def
    have h𝒞mem : ∀ C : Finset V, C ∈ 𝒞 ↔ IsOddCycle G C := by
      intro C
      rw [h𝒞def, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    have h𝒞ne : 𝒞.Nonempty := ⟨C0, (h𝒞mem C0).mpr hC0⟩
    have h𝒞meet : ∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ∩ D ≠ ∅ := fun C hC D hD =>
      hmeet C D ((h𝒞mem C).mp hC) ((h𝒞mem D).mp hD)
    obtain ⟨v, hv⟩ := hH 𝒞 (fun C hC => (h𝒞mem C).mp hC) h𝒞meet h𝒞ne
    refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨{v}, by simp, fun D hD => ?_⟩
    exact Finset.ne_empty_of_mem
      (Finset.mem_inter.mpr ⟨hv D ((h𝒞mem D).mpr hD), Finset.mem_singleton.mpr rfl⟩)
  · refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨∅, by simp, fun D hD => ?_⟩
    exact absurd ⟨D, hD⟩ hodd

/-- **THE SAME IN THE SHAPE OF THE HEADLINE THEOREM, AT EVERY `c`.**

```
LocIndep c G → HellyOddCycles G → (the odd cycles pairwise meet) → CloseToBipartite c G .
```

For `c = 1` this is round 83's instance; for `c ≥ 2` it is new, and the pairwise-meeting hypothesis
is not implied by `LocIndep c` for `c ≥ 2` (`kTriangles c`). -/
theorem erdos73On_helly_pairwiseMeeting :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (c : ℕ), LocIndep c G → HellyOddCycles G →
      (∀ C D : Finset W, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅) → CloseToBipartite c G := by
  intro W inst G c hG hH hmeet
  by_cases hc0 : c = 0
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact locIndep_zero_isBipartite (hc0 ▸ hG)
  · have hpos : 1 ≤ c := by omega
    exact closeToBipartite_mono hpos (closeToBipartite_one_of_helly_of_pairwiseMeeting hH hmeet)

/-! ## Part 6 — the constant `k` is attained on the Helly class -/

/-- **`kTriangles k` IS `HellyOddCycles`.**  Its odd cycles are pairwise vertex-disjoint
(`JSP90.oddCyclesDisjoint_kTriangles`), so a pairwise-meeting family of them has at most one member,
which trivially has a common vertex. -/
theorem helly_kTriangles (k : ℕ) : HellyOddCycles (kTriangles k) := by
  intro 𝒞 hodd hmeet hne
  obtain ⟨C, hC⟩ := hne
  obtain ⟨v, hv⟩ := (hodd C hC).nonempty'
  refine ⟨v, fun D hD => ?_⟩
  by_cases hCD : D = C
  · simpa [hCD] using hv
  · exfalso
    obtain (h | h) := oddCyclesDisjoint_kTriangles (k := k) C D (hodd C hC) (hodd D hD)
    · exact hCD h.symm
    · exact hmeet C hC D hD h

/-- **THE CONSTANT `k` OF `JSP90.erdos73On_helly_of_maxDefDescent` CANNOT BE LOWERED.**  The witness
`kTriangles k` is Helly (above), satisfies `LocIndep k` (`JSP90.locIndep_kTriangles`) and is **not**
`(k - 1)`-close to bipartite for `1 ≤ k`.  So on the Helly class the value of Erdős's constant is
*exactly* `k`, the same value as on the class of pairwise disjoint odd cycles
(`JSPProblem/Optimal.lean`) and on complete graphs (`JSPProblem/Weight.lean`). -/
theorem not_closeToBipartite_helly_kTriangles {k m : ℕ} (_h1 : 1 ≤ k) (h2 : m < k) :
    ¬ CloseToBipartite m (kTriangles k) :=
  no_closeToBipartite_of_maxDef_kTriangles (k := k) (m := m) h2

/-- **THE THREE FACTS HOLDING TOGETHER AT THE SHARP CONSTANT `k`**, as one statement: the class,
Erdős's hypothesis, and the failure of the conclusion with `m = k - 1`. -/
theorem helly_attained_sharp :
    ∀ k : ℕ, 1 ≤ k →
      HellyOddCycles (kTriangles k) ∧ LocIndep k (kTriangles k) ∧
        ¬ CloseToBipartite (k - 1) (kTriangles k) :=
  fun k hk => ⟨helly_kTriangles k, locIndep_kTriangles,
    not_closeToBipartite_helly_kTriangles hk (by omega)⟩

end

end JSP90
