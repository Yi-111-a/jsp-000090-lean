/-
# JSP-000090 — the **maximum-deficiency witnesses**: two of them overlap, and one vertex of them
# gives the descent

Attack family 32 (round 86).  New module, imported from the root module `JSPProblem.lean`.

## The statement of this round

`JSPProblem/Descent.lean` (round 84) reduced Erdős #73 on the Helly class with the *optimal*
constant `f(k) = k` to **one** statement about the maximum deficiency of a single vertex deletion,
`JSP90.HellyMaxDefDescent`, and left it unproved.  This round

* **proves the numerical half of that reduction** (Part 1) — any two maximum-deficiency witnesses
  of `G` overlap in at least `MaxDef G` vertices, so the family of witnesses is pairwise
  intersecting and two disjoint witnesses are impossible;
* **proves the descent in the form in which it is actually needed** (Part 2): one vertex common
  to all maximum-deficiency witnesses is enough, and *no* hypothesis on odd cycles is needed;
* **replaces the blocker by a strictly weaker one** (Part 3): `JSP90.HellyCommonMaxWitness`
  ("the maximum-deficiency witnesses of a Helly graph have a common vertex") implies round 84's
  `HellyMaxDefDescent`, so the new statement is sufficient for Erdős #73 on the Helly class and
  does not carry the extra demand that the vertex lie on an odd cycle;
* **proves the new statement for a class strictly larger than the Helly class** in the
  machine-checked range (Part 4), and records that the descent hypothesis is *not* automatic;
* **corrects two machine-checked results of round 84** that were artefacts of a bug in the
  verification program (below), one of which enlarges the target class.

## Verification done before formalising (exhaustive, in C; programs `s12.c`, `s13.c`, `s14.c`,
`s15.c`)

Over **all** graphs on `n ≤ 6` vertices (`2²¹` for `n = 7`; `27 591` of the `n = 6` graphs have an
odd cycle, `19 517` of those are Helly):

* **`VertexDescent` (`JSP90.HellyMaxDefDescent` restricted to Helly graphs) holds for every Helly
  graph on `n ≤ 7` vertices** (exhaustive, `870 530` non-bipartite Helly graphs at `n = 7`: 0
  violations), confirming round 84;
* it **fails without Helly**, first at `n = 6`: 120 graphs, all with `MaxDef = 1`, e.g. the graph
  with edges `01 02 04 05 12 13 15 23 24`, whose odd cycles include the triangles `012`, `015`,
  `024`, `123`: no single vertex meets all of them, so `MaxDef = 1 < τ = 2`, and the
  maximum-deficiency witnesses have empty intersection.  **Correction of round 84:** the
  *smallest* counterexample is **not** the diamond `K₄ − e`; the diamond satisfies the descent
  (`{0}` is a transversal, so `MaxDef (G − 0) = 0 ≤ 0 = MaxDef G − 1`);
* the descent is **equivalent** to "the maximum-deficiency witnesses have a common vertex": the
  number of violations of the two statements among all graphs on `n ≤ 6` vertices is the same
  (`120`), and both are `0` on the Helly class (`n ≤ 7`).  This is Part 2 below, proved in Lean;
* **König's property holds on the Helly class**: for every Helly graph on `n ≤ 7` vertices the exact
  least odd cycle transversal satisfies `τ = ν` (packing number) — 0 counterexamples (also 0 for
  `n = 8` at random), and it fails off the class.  **Correction of round 84**, which reported "360 Helly graphs with `τ > ν`": its
  `tau_` returned the cardinality of the *first transversal in numeric order*, which is an upper
  bound for `τ`, so `τ_upper > ν` is no evidence at all about `τ > ν`;
* König's property nevertheless **fails for Helly families of finite sets in general**
  (`s14.c`: 0 violations up to `m = 5`, `k = 5`, but the C5-ring family `A_i = {p_{i-1}, p_i}`,
  `i` mod 5, is Helly with `ν = 2` and `τ = 3`).  So the graph structure — not Helly alone — is what
  gives `τ = ν` here, which is why a structural lemma is still needed;
* **and the Helly class is *optimal* among these hypotheses** (`s15.c`, exhaustive at `n = 7`):
  the same statements hold for `n <= 6` vertices under the strictly weaker `TwoHellyOddCycles`
  ("three pairwise meeting odd cycles have a common vertex", `JSPProblem/Cactus.lean`), but they
  **fail already at `n = 7`** -- `840` graphs with `TwoHellyOddCycles`, `MaxDef = 1`, packing number
  `1` and transversal number `2`; the first is the graph on vertices `0...6` with edges
  `04 05 06 12 13 16 23 25 34`.  So the Helly property itself, not merely the absence of *rings of
  three*, is what the descent needs.  Part 4 records the refutation and keeps the conditional
  instance for the two-Helly class, so that no later round retries it.

## What is *not* proved

`JSP90.HellyCommonMaxWitness` -- "for every Helly graph of maximum deficiency at least one, the
maximum-deficiency witnesses have a common vertex".  It is the **single** remaining statement of
Erdős #73 on the Helly class: it is verified on all graphs with `n <= 7` vertices (0 violations of
it, and of each of the three statements checked alongside it in the header: König, `τ <= MaxDef`,
`VertexDescent`), while everything else about that class -- the heredity, the deficiency descent,
the numerical overlap of the witnesses, the induction, the sharpness of the constant `k` -- is
proved in Lean here and in rounds 83-84.
Its two-Helly version `JSP90.TwoHellyCommonMaxWitness` of Part 4 is **false** (see the header) and is
recorded only as a refutation.
-/

import JSPProblem.Descent

namespace JSP90

open Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance instDecidableEqWitness : DecidableEq V := Classical.decEq V

local instance instDecidableIsOddCycleWitness {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ## Part 1 — two maximum-deficiency witnesses overlap in at least `MaxDef G` vertices -/

/-- **A POSITIVE DEFICIENCY IS NEVER TRUNCATED.**  If `defOf G X = d ≥ 1` then
`X.card = d + 2 * α(G[X])`. -/
theorem card_eq_defOf_add_two_mul_indepCard {X : Finset V} {d : ℕ} (hd : 1 ≤ d)
    (hX : defOf G X = d) : X.card = d + 2 * indepCard G X := by
  have hdef : X.card - 2 * indepCard G X = d := by simpa only [defOf] using hX
  by_cases hle : 2 * indepCard G X ≤ X.card
  · have hsub : X.card - 2 * indepCard G X + 2 * indepCard G X = X.card :=
      Nat.sub_add_cancel hle
    omega
  · have hz : X.card - 2 * indepCard G X = 0 := by
      rw [Nat.sub_eq_zero_iff_le]
      omega
    omega

/-- **TWO MAXIMUM-DEFICIENCY WITNESSES OVERLAP IN AT LEAST `MaxDef G` VERTICES.**  If `X` and `Y`
both have deficiency exactly `MaxDef G = d ≥ 1`, then `d ≤ |X ∩ Y|`.

Indeed `α(G[X ∪ Y]) ≤ α(G[X]) + α(G[Y])` (`JSP90.indepCard_le_add`), so
`|X ∪ Y| − 2 α(G[X ∪ Y]) ≥ (|X| − 2 α(G[X])) + (|Y| − 2 α(G[Y])) − |X ∩ Y| = 2 d − |X ∩ Y|`,
while the left side is at most `d` by definition of `MaxDef G`; hence `d ≤ |X ∩ Y|`. -/
theorem card_inter_ge_maxDef {X Y : Finset V} (hpos : 1 ≤ MaxDef G)
    (hX : defOf G X = MaxDef G) (hY : defOf G Y = MaxDef G) :
    MaxDef G ≤ (X ∩ Y).card := by
  have hX' : X.card = MaxDef G + 2 * indepCard G X := card_eq_defOf_add_two_mul_indepCard hpos hX
  have hY' : Y.card = MaxDef G + 2 * indepCard G Y := card_eq_defOf_add_two_mul_indepCard hpos hY
  have hα : indepCard G (X ∪ Y) ≤ indepCard G X + indepCard G Y := indepCard_le_add X Y
  have hw : 2 * indepCard G (X ∪ Y) ≤ 2 * indepCard G X + 2 * indepCard G Y := by
    have h := Nat.mul_le_mul_left 2 hα
    omega
  have hcard : X.card + Y.card ≤ (X ∪ Y).card + (X ∩ Y).card := by
    have h := Finset.card_union_add_card_inter X Y
    omega
  have hle : (X ∪ Y).card - 2 * indepCard G (X ∪ Y) ≤ MaxDef G := le_maxDef G _
  have h1 : (X ∪ Y).card ≤ MaxDef G + 2 * indepCard G (X ∪ Y) :=
    (Nat.sub_le_iff_le_add).mp hle
  omega

/-- **NO TWO MAXIMUM-DEFICIENCY WITNESSES ARE DISJOINT.**  So the family of witnesses of
`MaxDef G ≥ 1` is a pairwise-intersecting family of vertex sets — in contrast with the family of
odd cycles, which is *not* pairwise intersecting in general (that is what Erdős–Pósa is about). -/
theorem inter_maxWitness_ne {X Y : Finset V} (hpos : 1 ≤ MaxDef G)
    (hX : defOf G X = MaxDef G) (hY : defOf G Y = MaxDef G) : X ∩ Y ≠ ∅ := by
  by_contra hcon
  have h0 : (X ∩ Y).card = 0 := Finset.card_eq_zero.mpr hcon
  have := card_inter_ge_maxDef hpos hX hY
  omega

/-- **EVERY MAXIMUM-DEFICIENCY WITNESS HAS AT LEAST `MaxDef G` VERTICES**, and it meets every odd
cycle (`JSP90.defOf_maxDef_inter_oddCycle_ne`): a witness of deficiency `d` is an odd cycle
transversal of size at least `d`. -/
theorem card_ge_maxDef_of_defOf_eq_maxDef {X : Finset V} (hX : defOf G X = MaxDef G) :
    MaxDef G ≤ X.card := by
  have hdef : X.card - 2 * indepCard G X = MaxDef G := by simpa only [defOf] using hX
  by_cases hle : 2 * indepCard G X ≤ X.card
  · have hsub : X.card - 2 * indepCard G X + 2 * indepCard G X = X.card :=
      Nat.sub_add_cancel hle
    omega
  · have hz : X.card - 2 * indepCard G X = 0 := by
      rw [Nat.sub_eq_zero_iff_le]
      omega
    omega

/-! ## Part 2 — the descent from a vertex common to all maximum-deficiency witnesses -/

/-- **A VERTEX COMMON TO ALL MAXIMUM-DEFICIENCY WITNESSES.**  `CommonMaxWitness G d` says that
some vertex belongs to every vertex set of deficiency exactly `d`. -/
noncomputable def CommonMaxWitness (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ v : V, ∀ X : Finset V, defOf G X = d → v ∈ X

/-- **EVERY VERTEX SET AVOIDING THE COMMON WITNESS HAS SMALLER DEFICIENCY.**  This is the whole
numerical content of the descent: a vertex set of deficiency `d` which avoids the common witness
vertex would itself be a witness. -/
theorem defOf_le_sub_one_of_not_mem {d : ℕ} {w : V} (hd : d = MaxDef G) (hpos : 1 ≤ d)
    (hw : ∀ X : Finset V, defOf G X = d → w ∈ X) {Y : Finset V} (hY : w ∉ Y) :
    defOf G Y ≤ d - 1 := by
  by_contra hn
  have hle : defOf G Y ≤ d := by
    have hle' := le_maxDef G Y
    omega
  have heq : defOf G Y = d := by omega
  exact hY (hw Y heq)

/-- **THE DEFICIENCY OF A VERTEX SET NOT CONTAINING `v` IS THE SAME IN `G` AND IN `G − {v}`.** -/
theorem defOf_deleteFinset_singleton_of_not_mem {v : V} {Y : Finset V} (hY : v ∉ Y) :
    defOf (deleteFinset G {v}) Y = defOf G Y := by
  have hsub : Y ⊆ Finset.univ \ {v} := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
    intro hxv
    have hxv' : x = v := by simpa using Finset.mem_singleton.mp hxv
    exact hY (hxv' ▸ hx)
  have h := defOf_induceFinset_of_subset (G := G) (U := Finset.univ \ {v}) (Y := Y) hsub
  simpa [deleteFinset] using h

/-- **THE RESIDUE `G - {v}` HAS NO WITNESS OF DEFICIENCY `d = MaxDef G`.**  The deficiency of a
vertex set of `G` *in the residue* is at most that of its intersection with the residue
(`JSP90.defOf_induceFinset_le_inter`), and that intersection avoids `v`; so if `v` is common to all
witnesses, no vertex set of the residue has deficiency `d`, and the maximum deficiency of the
residue is at most `d - 1`. -/
theorem defOf_deleteFinset_singleton_le {d : ℕ} {v : V} (hd : d = MaxDef G) (hpos : 1 ≤ d)
    (hw : ∀ X : Finset V, defOf G X = d → v ∈ X) (Y : Finset V) :
    defOf (deleteFinset G {v}) Y ≤ d - 1 := by
  have h1 := defOf_induceFinset_le_inter (G := G) (X := Finset.univ \ {v}) (Y := Y)
  have h3 : defOf (induceFinset G (Finset.univ \ {v})) Y = defOf (deleteFinset G {v}) Y := by
    simp [deleteFinset]
  rw [h3] at h1
  have hsub : (Finset.univ \ {v}) ∩ Y ⊆ Finset.univ \ {v} := Finset.inter_subset_left
  have h2 := defOf_induceFinset_of_subset (G := G) (U := Finset.univ \ {v})
    (Y := (Finset.univ \ {v}) ∩ Y) hsub
  rw [h2] at h1
  have hnotv : v ∉ Finset.univ \ {v} := by
    intro hcon
    rw [Finset.mem_sdiff] at hcon
    exact hcon.2 (Finset.mem_singleton.mpr rfl)
  have hnot : v ∉ (Finset.univ \ {v}) ∩ Y :=
    fun hcon => hnotv (Finset.mem_inter.mp hcon).1
  have hkey : defOf G ((Finset.univ \ {v}) ∩ Y) ≤ d - 1 :=
    defOf_le_sub_one_of_not_mem hd hpos (fun X hX => hw X hX) hnot
  exact h1.trans hkey

/-- **THE DESCENT: A COMMON WITNESS VERTEX DROPS THE MAXIMUM DEFICIENCY BY ONE.**

```
(∀ X, defOf G X = d → v ∈ X) → d = MaxDef G → 1 ≤ d → MaxDef (G - {v}) + 1 ≤ d .
```

No hypothesis on odd cycles, on the Helly property, on degrees, on connectivity or on cuts enters
here: this is a purely numerical statement about the maximum of `|X| - 2 α(G[X])`. -/
theorem maxDef_add_one_le_maxDef_delete_of_common {d : ℕ} (hd : d = MaxDef G) (hpos : 1 ≤ d)
    {v : V} (hv : ∀ X : Finset V, defOf G X = d → v ∈ X) :
    MaxDef (deleteFinset G {v}) + 1 ≤ d := by
  have hkey : MaxDef (deleteFinset G {v}) ≤ d - 1 :=
    maxDef_le (G := deleteFinset G {v}) (fun Y => defOf_deleteFinset_singleton_le hd hpos hv Y)
  omega

/-- **THE EQUIVALENCE WITH THE DESCENT: the maximum-deficiency witnesses have a common vertex if
and only if some vertex deletion drops `MaxDef` by one.**  This is what makes
`JSP90.CommonMaxWitness` the right statement to attack, and it is machine-checked on all graphs
with `n ≤ 6` vertices (see the header). -/
theorem commonWitness_iff_maxDef_descent (hpos : 1 ≤ MaxDef G) :
    CommonMaxWitness G (MaxDef G) ↔ ∃ v : V, MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, maxDef_add_one_le_maxDef_delete_of_common rfl hpos hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, fun X hX => ?_⟩
    by_contra hcon
    have hle : defOf G X ≤ MaxDef (deleteFinset G {v}) := by
      have hle' : defOf (deleteFinset G {v}) X ≤ MaxDef (deleteFinset G {v}) := le_maxDef _ _
      rw [defOf_deleteFinset_singleton_of_not_mem hcon] at hle'
      exact hle'
    have h1 : 1 ≤ MaxDef G := by
      have := hv
      omega
    have hlt : MaxDef (deleteFinset G {v}) ≤ MaxDef G - 1 := le_sub_of_add_le' hv
    omega


/-- **ERDŐS #73 FROM A COMMON WITNESS VERTEX: THE INDUCTION.**  If every Helly graph of maximum
deficiency `≥ 1` has a vertex common to all its maximum-deficiency witnesses, then a Helly graph of
deficiency at most `t` is `t`-close to bipartite.  The induction deletes the common witness vertex;
the residue is again Helly (Part 1 of `JSPProblem/Descent.lean`) and its maximum deficiency is one
smaller (the descent just proved).  This is the only place where the descent is used. -/
theorem closeToBipartite_maxDef_common_aux
    (hD : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), HellyOddCycles G →
      MaxDef G = 0 ∨ CommonMaxWitness G (MaxDef G)) :
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
    · obtain ⟨v, hv⟩ := (hD W inst G hH).resolve_left hb
      have hdesc : MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G :=
        maxDef_add_one_le_maxDef_delete_of_common rfl (by omega) hv
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

/-- **ERDŐS #73 ON THE HELLY CLASS, WITH THE CONSTANT `MaxDef G`, FROM THE COMMON WITNESS.**  In
words: *for a Helly graph, the least odd cycle transversal is at most the maximum deficiency*. -/
theorem closeToBipartite_maxDef_of_commonWitness {W : Type u} {inst : Fintype W}
    (G : SimpleGraph W) (hD : ∀ (W' : Type u) (_ : Fintype W') (G' : SimpleGraph W'),
      HellyOddCycles G' → MaxDef G' = 0 ∨ CommonMaxWitness G' (MaxDef G')) (hH : HellyOddCycles G) :
    CloseToBipartite (MaxDef G) G := by
  letI := inst
  exact closeToBipartite_maxDef_common_aux hD (MaxDef G) W G (le_refl _) hH

/-! ## Part 3 — the sharpest missing statement -/

/-- **THE SINGLE MISSING LEMMA FOR THE HELLY CLASS: the maximum-deficiency witnesses of a Helly
graph have a common vertex.**  (Round 84's `JSP90.HellyMaxDefDescent` asks for more — that the
common vertex lie on an odd cycle of `G` — and the next theorem proves that this statement implies
round 84's.) -/
noncomputable def HellyCommonMaxWitness : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), HellyOddCycles G →
    MaxDef G = 0 ∨ CommonMaxWitness G (MaxDef G)

/-- **THE NEW MISSING LEMMA IMPLIES ROUND 84's.**  So `JSP90.HellyCommonMaxWitness` is *sufficient*
for Erdős #73 on the Helly class, and is the weaker of the two statements: it makes no demand
about odd cycles. -/
theorem hellyCommonMaxWitness_of_hellyMaxDefDescent (hD : HellyMaxDefDescent.{u}) :
    HellyCommonMaxWitness.{u} := by
  intro W inst G hH
  by_cases hb : MaxDef G = 0
  · exact Or.inl hb
  · obtain ⟨C, v, hC, hvC, hdesc⟩ := hD W inst G hH (by omega)
    exact Or.inr ((commonWitness_iff_maxDef_descent (by omega)).mpr ⟨v, hdesc⟩)

/-- **ERDŐS #73 ON THE HELLY CLASS WITH THE OPTIMAL CONSTANT `k`, FROM THE COMMON WITNESS**:

```
LocIndep c G → HellyOddCycles G → CloseToBipartite c G    for every c .
```

That is round 83's `JSP90.HellyErdős73 id` as a theorem, not a hypothesis. -/
theorem erdos73On_helly_of_commonWitness (hD : HellyCommonMaxWitness.{u}) :
    HellyErdős73.{u} id := by
  intro W inst G c hG hH
  by_cases hz : MaxDef G = 0
  · refine closeToBipartite_mono (maxDef_le_of_locIndep hG) ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact maxDef_eq_zero_iff.mp hz
  · obtain ⟨v, hv⟩ := (hD W inst G hH).resolve_left hz
    exact closeToBipartite_mono (maxDef_le_of_locIndep hG)
      (closeToBipartite_maxDef_of_commonWitness (inst := inst) G
        (fun W' _ G' hH' => hD W' _ G' hH') hH)

/-- **THE INSTANCE AS A SINGLE IMPLICATION, in the shape of the catalogue question**: *if every
Helly graph of deficiency `≥ 1` has a vertex common to all its maximum-deficiency witnesses, then
every Helly graph of deficiency at most `k` is the union of a bipartite graph and `k` vertices.*

This is `JSP90.HellyErdős73 id` pointwise, i.e. Erdős Problem #73 — with the **optimal** constant
`f(k) = k` — on the class of graphs whose odd cycles form a Helly family.  (It cannot be stated as
`JSP90.Erdős73 k`: that statement ranges over *all* graphs, while the class hypothesis is essential
here.) -/
theorem closeToBipartite_of_helly_of_commonWitness (hD : HellyCommonMaxWitness.{u_1})
    {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hH : HellyOddCycles G) :
    CloseToBipartite k G :=
  erdos73On_helly_of_commonWitness hD V (inferInstance : Fintype V) G k hG hH

/-! ## Part 4 — the same descent on the strictly larger **two-Helly** class -/

/-- **TWO-HELLY IS INHERITED BY INDUCED SUBGRAPHS**, hence by residues: the odd cycles of
`induceFinset G s` are odd cycles of `G` (`JSP90.isOddCycle_induceFinset`), so a triple of pairwise
meeting odd cycles of the induced subgraph is a triple of pairwise meeting odd cycles of `G`. -/
theorem twoHelly_induceFinset {s : Finset V} (h : TwoHellyOddCycles G) :
    TwoHellyOddCycles (induceFinset G s) := by
  intro C D E hC hD hE hCD hDE hEC
  obtain ⟨v, hv⟩ := h C D E (isOddCycle_induceFinset hC).1 (isOddCycle_induceFinset hD).1
    (isOddCycle_induceFinset hE).1 hCD hDE hEC
  have h' : (v ∈ C ∧ v ∈ D) ∧ v ∈ E := by simpa only [Finset.mem_inter] using hv
  exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h'.1.1, h'.1.2⟩, h'.2⟩⟩

/-- **AND BY RESIDUES.**  This is what makes the induction of Part 4 go through. -/
theorem twoHelly_deleteFinset {X : Finset V} (h : TwoHellyOddCycles G) :
    TwoHellyOddCycles (deleteFinset G X) := by
  have h' : TwoHellyOddCycles (induceFinset G (Finset.univ \ X)) :=
    twoHelly_induceFinset (s := Finset.univ \ X) h
  simpa [deleteFinset] using h'

/-- **ERDŐS #73 ON THE TWO-HELLY CLASS, with an arbitrary function `f` of the parameter.**  The
class is `JSP90.TwoHellyOddCycles` of `JSPProblem/Cactus.lean`: *every three pairwise meeting odd
cycles have a common vertex*.  Round 83 proved `HellyOddCycles → TwoHellyOddCycles`
(`JSP90.twoHelly_of_helly`), so this is a **strictly larger** class than the Helly class.

**WARNING — this relaxation is refuted, and the conditional theorems that follow are kept only to
record it.**  Exhaustive search over all graphs with `n ≤ 7` vertices (`s15.c`) exhibits `840`
graphs that are two-Helly with `MaxDef = 1`, packing number `1` and transversal number `2`: the
first is the graph on vertices `0…6` with edges `04 05 06 12 13 16 23 25 34`.  So the corresponding
instance of Erdős #73 is **false** on the two-Helly class, and `JSP90.TwoHellyCommonMaxWitness`
below is **false** as well.  The Helly class is therefore optimal among the two classes considered
here. -/
noncomputable def TwoHellyErdős73 (f : ℕ → ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (c : ℕ),
    LocIndep c G → TwoHellyOddCycles G → CloseToBipartite (f c) G

/-- **THE TWO-HELLY VERSION OF THE DESCENT STATEMENT — WHICH IS FALSE.**  Every two-Helly graph
of maximum deficiency at least one *would* have a vertex common to all its maximum-deficiency
witnesses.  It implies the Helly version `JSP90.HellyCommonMaxWitness` (a Helly graph is two-Helly,
so this statement is the stronger one), and with it the whole of Erdős #73 with the optimal constant
`f(k) = k`.

But it is **false**: exhaustive search over all graphs with `n ≤ 7` vertices finds `840` two-Helly
graphs with `MaxDef = 1`, packing number `1` and transversal number `2`, in which no single vertex
lies in all maximum-deficiency witnesses (first witness: the graph on vertices `0…6` with edges
`04 05 06 12 13 16 23 25 34`).  It is stated as a `def` so that the *conditional* instances above
and below can be recorded; **do not** try to prove it and do not enlarge the target class to
two-Helly. -/
noncomputable def TwoHellyCommonMaxWitness : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), TwoHellyOddCycles G →
    MaxDef G = 0 ∨ CommonMaxWitness G (MaxDef G)

/-- **THE TWO-HELLY STATEMENT IMPLIES THE HELLY ONE**, since a Helly graph is two-Helly.  (So the
two-Helly statement is the stronger one, and its refutation leaves the Helly statement untouched.) -/
theorem hellyCommonMaxWitness_of_twoHellyCommonMaxWitness
    (hD : TwoHellyCommonMaxWitness.{u}) : HellyCommonMaxWitness.{u} := by
  intro W inst G hH
  exact hD W inst G (twoHelly_of_helly hH)

/-- **ERDŐS #73 WITH THE OPTIMAL CONSTANT `k` ON THE TWO-HELLY CLASS**, from the single statement
`JSP90.TwoHellyCommonMaxWitness` — which is false, so **no instance is obtained this way**: the
theorem is kept as the machine-checked record that the two-Helly class cannot replace the Helly
class. -/
theorem closeToBipartite_maxDef_twoHelly_aux
    (hD : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), TwoHellyOddCycles G →
      MaxDef G = 0 ∨ CommonMaxWitness G (MaxDef G)) :
    ∀ (t : ℕ) (W : Type u) (G : SimpleGraph W) [Fintype W], MaxDef G ≤ t → TwoHellyOddCycles G →
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
    · obtain ⟨v, hv⟩ := (hD W inst G hH).resolve_left hb
      have hdesc : MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G :=
        maxDef_add_one_le_maxDef_delete_of_common rfl (by omega) hv
      have hlt : MaxDef (deleteFinset G {v}) < t := by omega
      have hH' : TwoHellyOddCycles (deleteFinset G {v}) := twoHelly_deleteFinset hH
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

/-- **ERDŐS #73 ON THE TWO-HELLY CLASS WITH THE CONSTANT `MaxDef G`.** -/
theorem closeToBipartite_maxDef_of_twoHellyCommonWitness {W : Type u} {inst : Fintype W}
    (G : SimpleGraph W) (hD : TwoHellyCommonMaxWitness.{u}) (hH : TwoHellyOddCycles G) :
    CloseToBipartite (MaxDef G) G := by
  letI := inst
  exact closeToBipartite_maxDef_twoHelly_aux (fun W' _ G' hH' => hD W' _ G' hH')
    (MaxDef G) W G (le_refl _) hH

/-- **ERDŐS #73 WITH THE OPTIMAL CONSTANT `f(k) = k` ON THE TWO-HELLY CLASS**, from the single
missing lemma `JSP90.TwoHellyCommonMaxWitness`. -/
theorem erdos73On_twoHelly_of_commonWitness (hD : TwoHellyCommonMaxWitness.{u}) :
    TwoHellyErdős73.{u} id := by
  intro W inst G c hG hH
  by_cases hz : MaxDef G = 0
  · refine closeToBipartite_mono (maxDef_le_of_locIndep hG) ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact maxDef_eq_zero_iff.mp hz
  · exact closeToBipartite_mono (maxDef_le_of_locIndep hG)
      (closeToBipartite_maxDef_of_twoHellyCommonWitness (inst := inst) G hD hH)

/-- **THE SAME INSTANCE AS A SINGLE IMPLICATION**, on the two-Helly class.  Since
`JSP90.TwoHellyCommonMaxWitness` is false (see its docstring and the file header), no instance of
Erdős #73 is obtained this way; the theorem is kept so that the refutation is stated in the shape of
the headline theorem. -/
theorem closeToBipartite_of_twoHelly_of_commonWitness (hD : TwoHellyCommonMaxWitness.{u_1})
    {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hH : TwoHellyOddCycles G) :
    CloseToBipartite k G :=
  erdos73On_twoHelly_of_commonWitness hD V (inferInstance : Fintype V) G k hG hH

end

end JSP90
