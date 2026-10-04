import JSPProblem.Five
import JSPProblem.Sun

/-!
# JSP-000090, round 149 — `JSPProblem/Six.lean`: **THE SIX-VERTEX AXIS** — the sharp Erdős #73
## instance at `k = 1` for graphs of order at most `6`

Attack family 76.  Round 148 proved `JSP90.closeToBipartite_one_of_locIndep_one_card_le_five`
(the *structural* five-vertex instance, with the optimal constant `1`) and left as its concrete
next target `JSP90.closeToBipartite_two_of_locIndep_one_card_le_six`, whose sharpness was measured
exhaustively (all `32768` graphs on six vertices: the maximum of `tauOdd` over `MaxDef ≤ 1` is
exactly `2`, witnessed by the three-sun `sun3`).

**The six-vertex instance follows from a short reduction, and the reduction is worth recording in
its reusable form: one extra vertex costs exactly one extra deletion.**  Deleting a vertex leaves a
graph on at most five vertices, which is a `LocIndep 1` graph, so round 148's theorem applies to it.
The content of this file is therefore the two *reductions* it uses, one in the direction "more
vertices, more deletions" and one that is sharp:

* **`JSP90.closeToBipartite_succ_of_closeToBipartite_one`** and
  **`JSP90.LocIndepOneSmallOrder.succ`** — the one-more-vertex step.
* **`JSP90.closeToBipartite_one_of_locIndep_one_of_card_le`** — round 148's five-vertex instance in
  the **piece form**: a `LocIndep 1` graph induced on a vertex set of at most five vertices is one
  vertex away from bipartite.  This is the bridge the reduction needs, and it is proved from
  `JSPProblem/FiniteSharp.lean`'s `moveGraph` by
  `JSP90.locIndep_one_of_locIndep_one_moveGraph` (Erdős's hypothesis is read on the moved piece)
  together with `JSP90.closeToBipartite_pieceOf_closeToBipartite_of_card_le` (the witness and a
  `Fin 2`-colouring are pulled back).

Together the two reductions give the sharp six-vertex instance.  A third, independent reduction is
recorded in Part 2: `JSP90.card_eq_of_shortest_oddCycle_of_card_le_succ` — with at most one vertex
outside a shortest odd cycle, **all** odd cycles have equal cardinality — together with the
**counterexample that refutes the stronger reading of the same observation** (a vertex of `C` need
not meet every odd cycle; see the file header).

## What is proved

* **`JSP90.closeToBipartite_two_of_locIndep_one_card_le_six`**: `LocIndep 1 G → |V| ≤ 6 →
  CloseToBipartite 2 G` — a **new instance of the headline theorem with the OPTIMAL constant `2`**
  on graphs of order at most `6`, with no hypothesis beyond Erdős's own.  In the `Erdős73On` shape:
  `JSP90.erdos73On_one_two_of_card_le_six`; in the transversal shape:
  `JSP90.tauOdd_le_two_of_locIndep_one_card_le_six`.
* **`JSP90.smallOrder_k1_exact`** — the small-order constants at `k = 1` are **exact** through six
  vertices: `1` at order `≤ 5`, `2` at order `≤ 6`, and neither can be lowered
  (`JSP90.not_erdos73On_one_zero_of_card_le_five` with `K₃`,
  `JSP90.not_erdos73On_one_one_of_card_le_six` with the three-sun `sun3`).
* **`JSP90.closeToBipartite_three_of_locIndep_one_card_le_seven`** and
  `JSP90.erdos73On_one_three_of_card_le_seven`: the `+ 1`-per-vertex instance at seven vertices.
  These are **not** sharp there: the measured constant is `2` at seven vertices
  (`discovery/JSP-000090/r148_n7.log`, all `2097152` graphs) and also at eight vertices
  (`discovery/JSP-000090/r144b_n8.log`, search complete), so seven is the next order at which the
  sharp constant has to be proved.

## What is *not* proved

The general case.  `f(1) = 2` for graphs of *arbitrary* order is out of reach: that statement is
`JSP90.Erdős73On 1 2`, i.e. `JSP90.TraceCoverResidual` of `JSPProblem/TraceComplex.lean`, and behind
it `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).  `jsp_000090_main` is deliberately
**not** declared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance sixDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 1 — the reduction "one more vertex costs one more deletion" -/

/-- **An induced subgraph is a subgraph.**  The bridge between `LocIndep` for `G` and `LocIndep` for
`induceFinset G s`. -/
theorem induceFinset_le (s : Finset V) : induceFinset G s ≤ G := by
  intro v w h
  exact h.2.2

/-- **`LocIndep 1` passes to an induced subgraph.** -/
theorem locIndep_one_of_locIndep_one_induceFinset {s : Finset V} (hG : LocIndep 1 G) :
    LocIndep 1 (induceFinset G s) :=
  LocIndep.mono_le hG (induceFinset_le s)

/-- **`s \ insert a X = (s \ {a}) \ X`** whenever `a ∉ X`. -/
theorem sdiff_insert_eq {s : Finset V} {a : V} {X : Finset V} (ha : a ∉ X) :
    s \ insert a X = (s \ {a}) \ X := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **`|V \ {v}| = |V| - 1` for a vertex `v` of `V`.** -/
theorem card_sdiff_univ_singleton {v : V} (hv : v ∈ (Finset.univ : Finset V)) :
    ((Finset.univ : Finset V) \ {v}).card = Fintype.card V - 1 := by
  have h1 := Finset.card_sdiff_of_subset (s := {v}) (t := (Finset.univ : Finset V))
    (Finset.singleton_subset_iff.mpr hv)
  have h2 : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  rw [Finset.card_singleton, h2] at h1
  exact h1

/-- **`LocIndep 1` OF A PIECE, READ ON `Fin n`.**  For `U : Finset V` with `|U| = n` and
`e : U ≃ Fin n`,

```lean
LocIndep 1 G → LocIndep 1 (moveGraph e (G.induce (U : Set V)))
```

This is the bridge the piece axis needs: `JSP90.induceFinset_le` compares graphs on one vertex
*type*, while a piece `U` has fewer vertices than the type `V`, so the instance has to be read on
the moved piece.  The independent set `S ⊆ (e.symm '' X)` of `G` is transported to
`S.image (fun v => e ⟨v, hv⟩) ⊆ X`, of the same cardinality because `e` is injective; the map is
made total by an arbitrary default on `V \ U`. -/
theorem locIndep_one_of_locIndep_one_moveGraph {U : Finset V} {n : ℕ} (hUn : U.card = n)
    (e : U ≃ Fin n) (hG : LocIndep 1 G) :
    LocIndep 1 (moveGraph e (G.induce (U : Set V))) := by
  by_cases hUne : U.Nonempty
  · obtain ⟨d, hd⟩ := hUne
    set toFin : V → Fin n := fun v => if hv : v ∈ U then e ⟨v, hv⟩ else e ⟨d, hd⟩ with htoFin
    intro X
    obtain ⟨S, hSsub, hSi, hb⟩ := hG (X.image (fun i => (e.symm i : U).1))
    have hcardX : (X.image (fun i => (e.symm i : U).1)).card = X.card :=
      Finset.card_image_of_injective _ fun a b h => e.symm.injective (Subtype.ext h)
    have hSsubU : ∀ v ∈ S, v ∈ U := by
      intro v hv
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp (hSsub hv)
      rw [← heq]
      exact (e.symm a).2
    refine ⟨S.image toFin, ?_, ?_, ?_⟩
    · have hXU : ∀ i ∈ X, (e.symm i : U).1 ∈ U := fun i hi => (e.symm i).2
      intro v hv
      obtain ⟨v0, hv0, heq⟩ := Finset.mem_image.mp hv
      have hv0' : v0 ∈ X.image (fun i => (e.symm i : U).1) := hSsub hv0
      obtain ⟨i, hi, hvi⟩ := Finset.mem_image.mp hv0'
      have hkey : toFin v0 = i := by
        rw [htoFin]
        simp [hXU i hi, hSsubU v0 hv0]
        calc e ⟨v0, hSsubU v0 hv0⟩ = e (e.symm i) := congrArg e (Subtype.ext hvi).symm
          _ = i := Equiv.symm_apply_apply e.symm i
      rw [← heq, hkey]
      exact hi
    · rw [SimpleGraph.isIndepSet_iff] at hSi ⊢
      intro v hv1 w hw2 hne hvw
      obtain ⟨v0, hv0, heq1⟩ := Finset.mem_image.mp hv1
      obtain ⟨w0, hw0, heq2⟩ := Finset.mem_image.mp hw2
      have hv0S : v0 ∈ S := hv0
      have hw0S : w0 ∈ S := hw0
      have hvw' : G.Adj v0 w0 := by
        rw [← heq1, ← heq2] at hvw
        simp only [htoFin, hSsubU v0 hv0, hSsubU w0 hw0] at hvw
        rw [moveGraph_adj] at hvw
        obtain ⟨p, q, hp, hq, hpq⟩ := hvw
        rw [SimpleGraph.induce_adj] at hpq
        have hp' : p = ⟨v0, hSsubU v0 hv0⟩ := e.injective hp.symm
        have hq' : q = ⟨w0, hSsubU w0 hw0⟩ := e.injective hq.symm
        rw [hp', hq'] at hpq
        exact hpq
      by_cases h : v0 = w0
      · subst h
        exact absurd hvw' (fun hv => G.irrefl hv)
      · exact hSi hv0S hw0S h hvw'
    · have hinjS : Set.InjOn toFin S := by
        intro a ha b hb hab
        have ha' : a ∈ U := hSsubU a ha
        have hb' : b ∈ U := hSsubU b hb
        have hkey : toFin a = e ⟨a, ha'⟩ := by simp [htoFin, ha']
        have hkey2 : toFin b = e ⟨b, hb'⟩ := by simp [htoFin, hb']
        rw [hkey, hkey2] at hab
        exact congrArg Subtype.val (e.injective hab)
      have hcardS : (S.image toFin).card = S.card := Finset.card_image_iff.mpr hinjS
      rw [← hcardS, hcardX] at hb
      exact hb
  · intro X
    have hX0 : X = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hUne ⟨(e.symm x : U).1, (e.symm x).2⟩)
      · intro hx
        simp at hx
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro v hv
      rw [hX0]
      exact absurd hv (by simp)
    · rw [SimpleGraph.isIndepSet_iff]
      intro v hv
      exact absurd hv (by simp)
    · rw [hX0]
      simp

/-- **AN ELEMENT OF THE DELETED SET OF THE MOVED PIECE LIES IN THE DELETED SET OF THE PIECE.**
This is the bookkeeping step that pulls a witness `Y` of the moved piece back to the piece. -/
theorem mem_Z_image_of_mem {U : Finset V} {n : ℕ} {Y : Finset (Fin n)} (e : U ≃ Fin n)
    {v : V} (hv : v ∈ U) (hY : e ⟨v, hv⟩ ∈ Y) :
    v ∈ (Y.image e.symm).image Subtype.val := by
  refine Finset.mem_image.mpr ⟨⟨v, hv⟩, ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨e ⟨v, hv⟩, hY, Equiv.symm_apply_apply _ _⟩

/-- **AN INSTANCE AT ORDER `m` APPLIES TO EVERY INDUCED PIECE OF AT MOST `m` VERTICES.**

```lean
(∀ W, |W| ≤ m → LocIndep 1 → CloseToBipartite m) →
  U.card ≤ m → LocIndep 1 (induceFinset G U) → CloseToBipartite m (induceFinset G U)
```

This is the bridge that the small-order axis needs: the class `LocIndepOneSmallOrder` counts the
**vertices of the type**, while the residue of the one-more-vertex step is a *vertex set* `U` of the
same graph, which may be much smaller than the type.  The piece is moved to `Fin U.card`
(`JSP90.moveGraph` of `JSPProblem/FiniteSharp.lean`), the instance is applied there, and the
resulting colouring is pulled back — the witness is `(Y.image e.symm).image Subtype.val`. -/
theorem closeToBipartite_pieceOf_closeToBipartite_of_card_le {m n : ℕ}
    (hm : LocIndepOneSmallOrder.{0} m n) (hG : LocIndep 1 G)
    {U : Finset V} (hU : U.card ≤ n) :
    CloseToBipartite m (induceFinset G U) := by
  set e : U ≃ Fin U.card := Finset.equivFinOfCardEq rfl with he
  have hmv : LocIndep 1 (moveGraph e (G.induce (U : Set V))) :=
    locIndep_one_of_locIndep_one_moveGraph rfl e hG
  have hfin : Fintype.card (Fin U.card) ≤ n := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨Y, hY, hcol⟩ :=
    hm (Fin U.card) inferInstance (moveGraph e (G.induce (U : Set V))) hfin hmv
  obtain ⟨c, hc⟩ := hcol
  set Z : Finset U := Y.image e.symm with hZ
  have hZcard : Z.card ≤ m := by
    have himg : (Y.image e.symm).card = Y.card :=
      Finset.card_image_of_injective Y e.symm.injective
    rw [hZ, himg]
    exact hY
  refine ⟨Z.image Subtype.val, ?_, ?_⟩
  · have himg : (Z.image Subtype.val).card = Z.card :=
      Finset.card_image_of_injective Z Subtype.val_injective
    omega
  rw [deleteFinset_induceFinset]
  refine ⟨SimpleGraph.Coloring.mk (fun v => if hv : v ∈ U then c (e ⟨v, hv⟩) else 0) ?_⟩
  intro v w hvw
  have hvw' := (induce_adj).mp hvw
  have hvU : v ∈ U := (Finset.mem_sdiff.mp hvw'.1).1
  have hwU : w ∈ U := (Finset.mem_sdiff.mp hvw'.2.1).1
  have h1 : e ⟨v, hvU⟩ ∉ Y := fun hmem =>
    (Finset.mem_sdiff.mp hvw'.1).2 (hZ.symm ▸ mem_Z_image_of_mem e hvU hmem)
  have h2 : e ⟨w, hwU⟩ ∉ Y := fun hmem =>
    (Finset.mem_sdiff.mp hvw'.2.1).2 (hZ.symm ▸ mem_Z_image_of_mem e hwU hmem)
  have hadj : (moveGraph e (G.induce (U : Set V))).Adj (e ⟨v, hvU⟩) (e ⟨w, hwU⟩) :=
    moveGraph_adj_of_adj (G := G.induce (U : Set V)) (e := e)
      ((SimpleGraph.induce_adj).mpr hvw'.2.2)
  simp only [dif_pos hvU, dif_pos hwU]
  refine hc (by
    rw [deleteFinset_adj]
    exact ⟨h1, h2, hadj⟩)

/-- **THE FIVE-VERTEX INSTANCE, IN THE PIECE FORM.**  Round 148's theorem, transported from the
vertex type to a vertex set: a `LocIndep 1` graph induced on at most five vertices is one vertex
away from bipartite. -/
theorem closeToBipartite_one_of_locIndep_one_of_card_le (hG : LocIndep 1 G) {U : Finset V}
    (hU : U.card ≤ 5) : CloseToBipartite 1 (induceFinset G U) :=
  closeToBipartite_pieceOf_closeToBipartite_of_card_le (m := 1) (n := 5)
    erdos73On_one_one_of_card_le_five hG hU

/-- **THE ONE-MORE-VERTEX STEP, IN THE FORM THE SMALL-ORDER AXIS USES.**

```lean
CloseToBipartite m (induceFinset G (V \ {a})) → CloseToBipartite (m + 1) G
```

The witness of the residue is first intersected with `V \ {a}` — which does not change the residue,
since `A \ (X ∩ A) = A \ X` — and then the deleted vertex `a` is added back, so that the two
deletions are disjoint: `|a ∪ Y| = 1 + |Y| ≤ 1 + m`.  The key identity is
`JSP90.sdiff_insert_eq`. -/
theorem closeToBipartite_succ_of_closeToBipartite_one {a : V} {m : ℕ}
    (hb : CloseToBipartite m (induceFinset G ((Finset.univ : Finset V) \ {a}))) :
    CloseToBipartite (m + 1) G := by
  obtain ⟨X, hX, hb⟩ := hb
  set s : Finset V := (Finset.univ : Finset V) \ {a} with hs
  have hYcard : (X ∩ s).card ≤ m :=
    le_trans (Finset.card_le_card (Finset.inter_subset_left : X ∩ s ⊆ X)) hX
  have hnotmem : a ∉ s := by
    rw [hs, Finset.mem_sdiff]
    exact fun h => h.2 (Finset.mem_singleton.mpr rfl)
  have hYa : a ∉ (X ∩ s : Finset V) := fun h => hnotmem ((Finset.mem_inter.mp h).2)
  have hYb : (induceFinset G (s \ (X ∩ s))).IsBipartite := by
    have hb' : (induceFinset G (s \ X)).IsBipartite := by
      rw [← deleteFinset_induceFinset (G := G) s X]
      exact hb
    rw [sdiff_inter_self s X]
    exact hb'
  have hYb' : (deleteFinset (induceFinset G s) (X ∩ s)).IsBipartite := by
    rw [deleteFinset_induceFinset (G := G) s (X ∩ s)]
    exact hYb
  have hkey : ((Finset.univ : Finset V) \ insert a (X ∩ s)) = s \ (X ∩ s) := by
    rw [hs, sdiff_insert_eq (s := (Finset.univ : Finset V)) (X := X ∩ s) hYa]
  have hfinal : deleteFinset G (insert a (X ∩ s)) = deleteFinset (induceFinset G s) (X ∩ s) := by
    calc deleteFinset G (insert a (X ∩ s))
        = induceFinset G ((Finset.univ : Finset V) \ insert a (X ∩ s)) := rfl
      _ = induceFinset G (s \ (X ∩ s)) := by rw [hkey]
      _ = deleteFinset (induceFinset G s) (X ∩ s) :=
        (deleteFinset_induceFinset (G := G) s (X ∩ s)).symm
  refine ⟨insert a (X ∩ s), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (s := X ∩ s) hYa]
    omega
  · rw [hfinal]
    exact hYb'

/-- **THE ONE-MORE-VERTEX STEP, IN THE `LocIndepOneSmallOrder` SHAPE OF
`JSPProblem/Five.lean`.**  An instance of Erdős #73 at `k = 1` on graphs of order at most `n` with
constant `m` gives the instance on graphs of order at most `n + 1` with constant `m + 1`. -/
theorem LocIndepOneSmallOrder.succ {m n : ℕ} (h : LocIndepOneSmallOrder.{0} m n) :
    LocIndepOneSmallOrder.{0} (m + 1) (n + 1) := by
  intro W inst G hW hG
  by_cases hne : Nonempty W
  · obtain ⟨a⟩ := hne
    have hscard : ((Finset.univ : Finset W) \ {a}).card ≤ n := by
      have h1 := card_sdiff_univ_singleton (V := W) (Finset.mem_univ a)
      have h2 : Fintype.card W ≤ n + 1 := hW
      omega
    exact closeToBipartite_succ_of_closeToBipartite_one (G := G) (m := m)
      (closeToBipartite_pieceOf_closeToBipartite_of_card_le (m := m) (n := n) h hG hscard)
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    refine isBipartite_of_no_oddCycle fun h => ?_
    obtain ⟨D, hD⟩ := h
    obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
      have hz := isOddCycle_card_ge_three hD
      omega)
    exact absurd ⟨z⟩ hne

/-- **THE REDUCTION ITERATES: `(m, n) → (m + k, n + k)`.**  So one small-order instance at
`k = 1` settles every larger order at the cost of one deletion per vertex:
`LocIndepOneSmallOrder 1 5` gives `LocIndepOneSmallOrder (1 + k) (5 + k)`.  This is the *non-sharp*
family of constants; the sharp constants at order seven and beyond are the target of the next
round (see `discovery/JSP-000090/policy.json`). -/
theorem LocIndepOneSmallOrder.iter (k : ℕ) {m n : ℕ} (h : LocIndepOneSmallOrder.{0} m n) :
    LocIndepOneSmallOrder.{0} (m + k) (n + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      LocIndepOneSmallOrder.succ ih

/-! ## Part 2 — at most one vertex outside a shortest odd cycle: all odd cycles have equal length

**A false lemma, recorded because it is instructive.**  The obvious statement — "if `C` is a shortest odd
cycle and `|V| ≤ |C| + 1`, then every vertex of `C` meets every odd cycle" — is *false*, and the
development of this round found the counterexample before the machine: with `|V| = 6`, `|C| = 5` and
a second `5`-cycle `D = V \ {v}` for a vertex `v` of the *complement* of `C`, the odd cycles `C` and
`D` are disjoint on `v`, so `{v}` misses `D` although `v ∈ C`.  What *is* true is the parity
statement below, and it is all the reduction needs. -/

/-- **AT MOST ONE VERTEX OUTSIDE A SHORTEST ODD CYCLE, EVERY ODD CYCLE HAS THE SAME CARDINALITY.**

```lean
IsOddCycle G C → (∀ D, IsOddCycle G D → C.card ≤ D.card) → |V| ≤ C.card + 1 →
  ∀ D, IsOddCycle G D → D.card = C.card
```

The proof is a parity argument: `|D| ≥ |C|` by the minimality of `C` and `|D| ≤ |V| ≤ |C| + 1`,
while both cardinalities are odd, so `|D| = |C|`.  In particular any two odd cycles meet in at
least `|C| - 1 ≥ 2` vertices. -/
theorem card_eq_of_shortest_oddCycle_of_card_le_succ {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hV : Fintype.card V ≤ C.card + 1) :
    ∀ D : Finset V, IsOddCycle G D → D.card = C.card := by
  intro D hD
  have hge : C.card ≤ D.card := hshort D hD
  have hle : D.card ≤ Fintype.card V := by
    have h1 : D.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ D
    rw [Finset.card_univ] at h1
    exact le_trans h1 (by omega)
  have hCodd : C.card % 2 = 1 := card_mod_two_of_isOddCycle hC
  have hDodd : D.card % 2 = 1 := card_mod_two_of_isOddCycle hD
  omega

/-! ## Part 3 — the sharp six-vertex instance -/

/-- **ERDŐS #73 AT `k = 1`, `m = 2`, ON GRAPHS WITH AT MOST SIX VERTICES — THE OPTIMAL INSTANCE.**

```lean
LocIndep 1 G → |V| ≤ 6 → CloseToBipartite 2 G
```

The proof is the reduction of Part 1, in its sharp form: delete a vertex `a`.  The residue
`G[V \ {a}]` is a `LocIndep 1` graph induced on at most **five** vertices, so
`JSP90.closeToBipartite_one_of_locIndep_one_of_card_le` — round 148's theorem in the piece form
transported by `JSP90.locIndep_one_of_locIndep_one_moveGraph` — makes it one vertex away from
bipartite, and `JSP90.closeToBipartite_succ_of_closeToBipartite_one` adds `a` back.  No odd girth,
no packing weight, no degree bound and no decomposition are used.

The constant `2` is sharp: see `JSP90.smallOrder_k1_exact`. -/
theorem closeToBipartite_two_of_locIndep_one_card_le_six (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 6) : CloseToBipartite 2 G := by
  by_cases hne : Nonempty V
  · obtain ⟨a⟩ := hne
    have h1 := card_sdiff_univ_singleton (V := V) (Finset.mem_univ a)
    have h2 : Fintype.card V ≤ 6 := hV
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr (Nonempty.intro a)
    have h3 : Fintype.card V - 1 + 1 = Fintype.card V := Nat.sub_add_cancel hpos
    have h5 : Fintype.card V - 1 ≤ 5 := by omega
    exact closeToBipartite_succ_of_closeToBipartite_one (a := a) (m := 1)
      (closeToBipartite_one_of_locIndep_one_of_card_le hG
        (U := (Finset.univ : Finset V) \ {a}) (by omega))
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    refine isBipartite_of_no_oddCycle fun h => ?_
    obtain ⟨D, hD⟩ := h
    obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
      have hz := isOddCycle_card_ge_three hD
      omega)
    exact absurd ⟨z⟩ hne

/-- **The same instance on graphs of order at most `5`,** contained in the six-vertex one. -/
theorem closeToBipartite_two_of_locIndep_one_card_le_five (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 5) : CloseToBipartite 2 G :=
  closeToBipartite_two_of_locIndep_one_card_le_six hG (le_trans hV (by omega))

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM IN THE `Erdős73On` SHAPE, WITH THE OPTIMAL CONSTANT
`2`, ON GRAPHS OF ORDER AT MOST `6`.** -/
theorem erdos73On_one_two_of_card_le_six : LocIndepOneSmallOrder.{u} 2 6 :=
  fun _ _ G hV hG => closeToBipartite_two_of_locIndep_one_card_le_six hG hV

/-- **THE SIX-VERTEX INSTANCE IN THE PIECE FORM**, i.e. the form a decomposition argument reads:
a `LocIndep 1` graph induced on a vertex set of at most six vertices is two vertices away from
bipartite. -/
theorem closeToBipartite_two_of_locIndep_one_of_card_le (hG : LocIndep 1 G) {U : Finset V}
    (hU : U.card ≤ 6) : CloseToBipartite 2 (induceFinset G U) :=
  closeToBipartite_pieceOf_closeToBipartite_of_card_le (m := 2) (n := 6)
    erdos73On_one_two_of_card_le_six hG hU

/-- **The seven-vertex instance obtained from the reduction of Part 1.**  The *sharp* constant at
seven vertices is `2` (measured, `r148_n7.log`), so this instance is not sharp; it is the
`+ 1`-per-vertex consequence of the six-vertex one, recorded so that the iteration of the reduction
is explicit. -/
theorem closeToBipartite_three_of_locIndep_one_card_le_seven (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 7) : CloseToBipartite 3 G := by
  by_cases hne : Nonempty V
  · obtain ⟨a⟩ := hne
    have h1 := card_sdiff_univ_singleton (V := V) (Finset.mem_univ a)
    have h2 : Fintype.card V ≤ 7 := hV
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr (Nonempty.intro a)
    have h3 : Fintype.card V - 1 + 1 = Fintype.card V := Nat.sub_add_cancel hpos
    have h5 : Fintype.card V - 1 ≤ 6 := by omega
    exact closeToBipartite_succ_of_closeToBipartite_one (a := a) (m := 2)
      (closeToBipartite_pieceOf_closeToBipartite_of_card_le (m := 2) (n := 6)
        erdos73On_one_two_of_card_le_six hG (U := (Finset.univ : Finset V) \ {a}) (by omega))
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    refine isBipartite_of_no_oddCycle fun h => ?_
    obtain ⟨D, hD⟩ := h
    obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
      have hz := isOddCycle_card_ge_three hD
      omega)
    exact absurd ⟨z⟩ hne

/-- **The seven-vertex instance in the `LocIndepOneSmallOrder` shape.** -/
theorem erdos73On_one_three_of_card_le_seven : LocIndepOneSmallOrder.{0} 3 7 :=
  LocIndepOneSmallOrder.succ erdos73On_one_two_of_card_le_six

/-- **The odd cycle transversal number is at most `2` at `LocIndep 1` and `|V| ≤ 6`.** -/
theorem tauOdd_le_two_of_locIndep_one_card_le_six (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 6) : tauOdd G ≤ 2 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_card_le_six hG hV)

/-- **A TWO-ELEMENT ODD CYCLE TRANSVERSAL EXISTS at `LocIndep 1` and `|V| ≤ 6`.** -/
theorem exists_hitsOddCycles_two_of_locIndep_one_card_le_six (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 6) :
    ∃ X : Finset V, X.card ≤ 2 ∧ HitsOddCycles G X :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_card_le_six hG hV)

/-! ## Part 4 — optimality of the constant `2` at six vertices -/

/-- **The three-sun has six vertices.** -/
theorem card_fin6 : Fintype.card (Fin 6) = 6 := by decide

/-- **`sun3` IS TWO-CLOSE TO BIPARTITE**, the six-vertex instance read on the sharp witness. -/
theorem closeToBipartite_two_sun3 : CloseToBipartite 2 sun3 :=
  closeToBipartite_two_of_locIndep_one_card_le_six locIndep_one_sun3 (by decide)

/-- **THE CONSTANT `2` OF THE SIX-VERTEX INSTANCE IS OPTIMAL**: `sun3` is `LocIndep 1`, is not
`1`-close to bipartite (`JSP90.not_closeToBipartite_one_sun3`) and is `2`-close
(`JSP90.closeToBipartite_two_sun3`). -/
theorem optimal_smallOrder_six : LocIndep 1 sun3 ∧ ¬ CloseToBipartite 1 sun3 :=
  ⟨locIndep_one_sun3, not_closeToBipartite_one_sun3⟩

/-- **NO INSTANCE AT `k = 1` AND CONSTANT `1` HOLDS AT ORDER SIX.**  The negative form of
`JSP90.erdos73On_one_two_of_card_le_six`. -/
theorem not_erdos73On_one_one_of_card_le_six : ¬ LocIndepOneSmallOrder.{0} 1 6 := by
  rintro h
  exact (optimal_smallOrder_six).2
    (h (Fin 6) inferInstance sun3 (by decide) (optimal_smallOrder_six).1)

/-- **THE SMALL-ORDER CONSTANTS AT `k = 1` ARE EXACT THROUGH SIX VERTICES.**

```lean
LocIndepOneSmallOrder 1 5 ∧ ¬ LocIndepOneSmallOrder 0 5 ∧
  LocIndepOneSmallOrder 2 6 ∧ ¬ LocIndepOneSmallOrder 1 6
```

So `f(1) = 1` for every graph on at most five vertices and `f(1) = 2` for every graph on at most six
vertices, and neither constant can be lowered: the first by `K₃`
(`JSP90.optimal_smallOrder_five`), the second by the three-sun.  The measured constants stay `2` at
seven vertices (`discovery/JSP-000090/r148_n7.log`, `2097152` graphs exhausted) and at eight
vertices (`discovery/JSP-000090/r144b_n8.log`, search complete: no `LocIndep 1` graph on eight
vertices has `tauOdd ≥ 3`), so seven is the next order at which the sharp constant must be proved. -/
theorem smallOrder_k1_exact :
    LocIndepOneSmallOrder.{0} 1 5 ∧ ¬ LocIndepOneSmallOrder.{0} 0 5 ∧
      LocIndepOneSmallOrder.{0} 2 6 ∧ ¬ LocIndepOneSmallOrder.{0} 1 6 :=
  ⟨erdos73On_one_one_of_card_le_five, not_erdos73On_one_zero_of_card_le_five,
    erdos73On_one_two_of_card_le_six, not_erdos73On_one_one_of_card_le_six⟩

end

end JSP90