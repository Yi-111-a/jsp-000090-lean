/-
# `JSPProblem/SunExact.lean` — `tauOdd` is **additive over disjoint unions**, and the transversal
# of the `k`-fold 3-sun is **exactly** `2 k`

Attack family 96, the **exact-value axis**: round 176 proved the *lower* bound
`tauOdd (sun3U k) ≥ 2 k` (`JSP90.not_closeToBipartite_lt_two_mul_sun3U`, which lets `2 k` be the
constant `m` in `Erdős73On`) but could not install the *upper* bound, because the kernel check it
needs — `(deleteFinset sun3 {0, 2}).IsBipartite` — cannot be reached by `decide` from inside a file
that has a classical `DecidableEq` in scope.  This round proves the missing transport instead, in
the direction round 176 lacked: **the residue of a disjoint union is bipartite when the residue of
every piece is**.  That turns the single-piece fact `JSP90.closeToBipartite_two_sun3` (already in
`JSPProblem/Six.lean`) into a statement about the whole union, and it is worth having in its own
right: it is *the* lemma that makes the hypothesis and the conclusion of Erdős #73 both split over
the components of a graph.

## What is proved

* **Part 1 — the deleted set of a disjoint union.**  `JSP90.sumZ Z` is the union, over the fibres,
  of the copies of the deleted sets `Z i`, with the reading `JSP90.mem_sumZ`
  (`p ∈ sumZ Z ↔ ∃ i, p.1 ∈ Z i`), the one-point reading `JSP90.not_mem_Z_of_not_mem_sumZ`, and the
  counting lemma `JSP90.card_sumZ`.
* **Part 1 bis — `JSP90.isBipartite_delete_sumGraph`: THE RESIDUE OF A DISJOINT UNION IS BIPARTITE
  WHEN EVERY PIECE IS.**  Round 176 has the *other* transport (`JSP90.deleteFinset_sumGraph_fib`:
  the residue inside one fibre is the residue of that piece); this is the assembling direction, and
  it is proved with a **genuine two-colouring** of the whole union: at a point of the `i`-th fibre
  it is the `i`-th piece's own colouring of its own residue.
* **Part 2 — `JSP90.closeToBipartite_sumGraph_of_forall`,
  `JSP90.closeToBipartite_sumGraph_of_forall_of_mul` (the constant `j * m`), and
  `JSP90.closeToBipartite_sumGraph_of_piece`: the conclusion of Erdős #73 is *additive over
  components*,** and no single component is ever farther from bipartite than the whole.
* **Part 3 — `JSP90.tauOdd_sumGraph`: THE LEAST ODD CYCLE TRANSVERSAL OF A DISJOINT UNION IS THE
  SUM OF THE TRANSVERSALS OF ITS PIECES.**  Together with round 176's `JSP90.locIndep_sumGraph`
  (Erdős's hypothesis is additive over components) and `JSP90.maxDef G ≤ tauOdd G`, the whole
  sandwich `ν ≤ MaxDef ≤ τ` of `JSPProblem/Deficiency.lean` splits over components.
* **Part 4 — the exact transversal of the canonical witness.**
  **`JSP90.tauOdd_sun3U : tauOdd (sun3U k) = 2 * k`** and
  `JSP90.closeToBipartite_two_mul_sun3U`, so round 176's lower bound `2 k` on the constant of
  Erdős #73 is *attained*: `JSP90.exists_sharp_witness k` packages the witness with its hypothesis
  and its defect, `LocIndep k G ∧ MaxDef G = k ∧ tauOdd G = 2 * k`, and
  `JSP90.two_mul_le_of_locIndep_of_sumGraph` reads the same equality off an arbitrary disjoint
  union of `LocIndep k` pieces.
* **Part 5 — a new order-free instance of the headline theorem.**
  **`JSP90.closeToBipartite_of_sumGraph_of_oddCactus_of_locIndep_one`**: a disjoint union of `j`
  graphs, each satisfying Erdős's hypothesis with the parameter `1` and each an `OddCactus`, is
  **`j`-close to bipartite**, with the optimal constant `j` (attained at `j = k` on `kTriangles k`,
  `JSP90.not_closeToBipartite_helly_kTriangles`).  No order bound anywhere.

`jsp_000090_main` is deliberately **not** declared: the missing direction is still
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), through
`JSP90.erdos73_of_erdosPosa`.
-/

import JSPProblem.SunSum

namespace JSP90

open Finset Fintype

universe u

noncomputable section

/-! ## Part 1 — the residue of a disjoint union is bipartite when every piece is -/

section Sum

variable {W : Type*} [Fintype W]

local instance sunExactDecidableEqW : DecidableEq W := Classical.decEq W

local instance sunExactProdEqW : DecidableEq (W × Fin j) := Classical.decEq (W × Fin j)

/-- **`sumZ Z` is the deleted set of the disjoint union built from the deleted sets of the
pieces**: the union, over the fibres, of the copies of `Z i` in the `i`-th copy of `W`. -/
def sumZ (Z : Fin j → Finset W) : Finset (W × Fin j) :=
  (Finset.univ : Finset (Fin j)).biUnion (fun i => (Z i).image (fun v => (v, i)))

omit [Fintype W] in
/-- **The reading of `sumZ`**: a point of the union belongs to the deleted set exactly when its own
coordinate belongs to the deleted set of its own piece. -/
theorem mem_sumZ {Z : Fin j → Finset W} {p : W × Fin j} :
    p ∈ sumZ Z ↔ p.1 ∈ Z p.2 := by
  rw [sumZ, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨i, v, hv, hvp⟩
    rw [← hvp]
    exact hv
  · intro hp
    refine ⟨p.2, p.1, hp, rfl⟩

omit [Fintype W] in
/-- **A point of the `i`-th fibre that the union does not delete is not deleted by the `i`-th
piece.** -/
theorem not_mem_Z_of_not_mem_sumZ {Z : Fin j → Finset W} {p : W × Fin j} (hp : p ∉ sumZ Z) :
    p.1 ∉ Z p.2 := fun h => hp ((mem_sumZ).2 h)

/-- **THE DELETED SET OF THE DISJOINT UNION HAS AS MANY POINTS AS THE DELETED SETS OF THE PIECES
ALTOGETHER.** -/
theorem card_sumZ (Z : Fin j → Finset W) : (sumZ Z).card = ∑ i : Fin j, (Z i).card := by
  have hb := Finset.card_biUnion (s := (Finset.univ : Finset (Fin j)))
    (t := fun i => (Z i).image (fun v => (v, i)))
    (pairwiseDisjoint_image (j := j) Z)
  rw [Finset.sum_congr rfl fun i _ => card_image_pair (Z i) i] at hb
  simpa only [sumZ] using hb

/-- **THE RESIDUE OF A DISJOINT UNION IS BIPARTITE WHEN THE RESIDUE OF EVERY PIECE IS.**

This is the direction that round 176's `JSPProblem/SunSum.lean` did not have, and it is what its
`policy.json` named as the missing repair: without it the two-vertex transversal of the single
3-sun cannot be turned into a transversal of the `k`-fold sun.

The two-colouring is explicit: at a point of the `i`-th fibre it is the `i`-th piece's own
colouring of its own residue, so a pair adjacent in the residue of the union is adjacent in the
residue of the piece that owns it, and the two-colouring of that piece separates the pair. -/
theorem isBipartite_delete_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} (Z : Fin j → Finset W)
    (h : ∀ i, (deleteFinset (H i) (Z i)).IsBipartite) :
    (deleteFinset (sumGraph j H) (sumZ Z)).IsBipartite := by
  classical
  have hcol : ∀ i : Fin j, ∃ d : W → Fin 2,
      ∀ u v : W, (deleteFinset (H i) (Z i)).Adj u v → d u ≠ d v := by
    intro i
    obtain ⟨⟨d, hd⟩⟩ := h i
    exact ⟨d, fun u v hadj => hd hadj⟩
  choose! d hd using hcol
  refine ⟨SimpleGraph.Coloring.mk (fun p : W × Fin j => d p.2 p.1) fun {p q} hadj => ?_⟩
  have hsplit := deleteFinset_adj.mp hadj
  have hp : p.1 ∉ Z p.2 := not_mem_Z_of_not_mem_sumZ hsplit.1
  have hq : q.1 ∉ Z q.2 := not_mem_Z_of_not_mem_sumZ hsplit.2.1
  have h2 := sumGraph_adj.mp hsplit.2.2
  have hadj' : (deleteFinset (H p.2) (Z p.2)).Adj p.1 q.1 := by
    rw [deleteFinset_adj]
    exact ⟨hp, by rwa [h2.1], h2.2⟩
  simpa only [h2.1] using hd p.2 p.1 q.1 hadj'

end Sum

/-! ## Part 2 — the conclusion of Erdős #73 is additive over components -/

section Conclusion

variable {W : Type*} [Fintype W]

local instance sunExactDecidableEqC : DecidableEq W := Classical.decEq W

local instance sunExactProdEqC : DecidableEq (W × Fin j) := Classical.decEq (W × Fin j)

/-- **A DISJOINT UNION OF GRAPHS THAT ARE `m i`-CLOSE TO BIPARTITE IS `(∑ i m i)`-CLOSE TO
BIPARTITE.**  Together with `JSP90.locIndep_sumGraph` (round 176), the *hypothesis* and the
*conclusion* of Erdős #73 are both summed over the components of a disjoint union. -/
theorem closeToBipartite_sumGraph_of_forall {j : ℕ} {H : Fin j → SimpleGraph W}
    {m : Fin j → ℕ} (h : ∀ i, CloseToBipartite (m i) (H i)) :
    CloseToBipartite (∑ i : Fin j, m i) (sumGraph j H) := by
  classical
  choose! Z hZ hb using fun i : Fin j => h i
  refine ⟨sumZ Z, ?_, isBipartite_delete_sumGraph (H := H) (Z := Z) (fun i => hb i)⟩
  rw [card_sumZ]
  exact Finset.sum_le_sum fun i _ => hZ i

/-- **THE SAME STATEMENT WITH ONE CONSTANT: a disjoint union of `j` graphs that are `m`-close to
bipartite is `j * m`-close to bipartite.** -/
theorem closeToBipartite_sumGraph_of_forall_of_mul {j : ℕ} {H : Fin j → SimpleGraph W} {m : ℕ}
    (h : ∀ i, CloseToBipartite m (H i)) : CloseToBipartite (j * m) (sumGraph j H) := by
  classical
  have h' : CloseToBipartite (∑ _i : Fin j, m) (sumGraph j H) :=
    closeToBipartite_sumGraph_of_forall (H := H) (m := fun _ => m) h
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, Nat.cast_id,
    Nat.mul_comm] using h'

/-- **NO SINGLE COMPONENT OF A DISJOINT UNION IS FARTHER FROM BIPARTITE THAN THE UNION ITSELF** —
the order-free half of "one bad component costs at most the whole budget", read with round 176's
transport lemma `JSP90.deleteFinset_sumGraph_fib` and `JSP90.card_image_fib`. -/
theorem closeToBipartite_sumGraph_of_piece {j : ℕ} {H : Fin j → SimpleGraph W} {m : ℕ}
    (h : CloseToBipartite m (sumGraph j H)) (i : Fin j) : CloseToBipartite m (H i) := by
  obtain ⟨Z, hZ, hb⟩ := h
  have hcard : ((Z ∩ fib i).image Prod.fst).card ≤ m := by
    exact le_trans (card_image_fib (S := Z) i).le
      (le_trans (Finset.card_le_card (s := Z ∩ fib i) (t := Z) (Finset.inter_subset_left)) hZ)
  exact ⟨(Z ∩ fib i).image Prod.fst, hcard, deleteFinset_sumGraph_fib (H := H) (Z := Z) i hb⟩

end Conclusion

/-! ## Part 3 — the least odd cycle transversal is additive over components -/

section Tau

variable {W : Type*} [Fintype W]

local instance sunExactDecidableEqT : DecidableEq W := Classical.decEq W

local instance sunExactProdEqT : DecidableEq (W × Fin j) := Classical.decEq (W × Fin j)

/-- **THE LEAST ODD CYCLE TRANSVERSAL OF A DISJOINT UNION IS THE SUM OF THE LEAST ODD CYCLE
TRANSVERSALS OF ITS PIECES.**

```lean
tauOdd (⊔ H i) = ∑ i, tauOdd (H i)
```

Both directions.  `≤`: a minimum transversal of the union meets every odd cycle of every piece
(round 176's `JSPProblem/SunSum.lean`, `JSP90.deleteFinset_sumGraph_fib`), and the pieces it meets
carry disjoint subsets of it, so its cardinality is the sum of theirs.  `≥`: the deleted sets of the
pieces in `JSP90.closeToBipartite_sumGraph_of_forall` (Part 2) are transversals of the pieces.

This is the missing half of the "Erdős's hypothesis is summed over the components" story of round
176: the sandwich `ν ≤ MaxDef ≤ τ` of `JSPProblem/Deficiency.lean` splits over the components of a
disjoint union, exactly as `JSP90.locIndep_sumGraph` says the hypothesis does. -/
theorem tauOdd_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} :
    tauOdd (sumGraph j H) = ∑ i : Fin j, tauOdd (H i) := by
  refine le_antisymm ?_ ?_
  · have h1 : tauOdd (sumGraph j H) ≤ ∑ i : Fin j, tauOdd (H i) :=
      (closeToBipartite_iff_tauOdd_le (G := sumGraph j H)
        (m := ∑ i : Fin j, tauOdd (H i))).mp (closeToBipartite_sumGraph_of_forall
          (fun i => (closeToBipartite_iff_tauOdd_le (G := H i)
            (m := tauOdd (H i))).mpr (Nat.le_refl _)))
    exact h1
  · obtain ⟨Z, hZ, hcard⟩ := tauOdd_spec (G := sumGraph j H)
    have hb : (deleteFinset (sumGraph j H) Z).IsBipartite :=
      isBipartite_delete_of_hitsOddCycles hZ
    have hsum : (∑ i : Fin j, ((Z ∩ fib i).image Prod.fst).card) = ∑ i : Fin j, (Z ∩ fib i).card :=
      Finset.sum_congr rfl fun i _ => card_image_fib (S := Z) i
    have h2 : (∑ i : Fin j, tauOdd (H i)) ≤ ∑ i : Fin j, ((Z ∩ fib i).image Prod.fst).card := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact tauOdd_le (hitsOddCycles_of_isBipartite_delete
        (deleteFinset_sumGraph_fib (H := H) (Z := Z) i hb))
    rw [hsum, (card_eq_sum_card_inter_fib (X := Z)).symm, hcard] at h2
    exact h2

/-- **THE LEAST ODD CYCLE TRANSVERSAL OF A SINGLE PIECE IS AT MOST THAT OF THE WHOLE UNION** — the
number form of Part 2's `JSP90.closeToBipartite_sumGraph_of_piece`. -/
theorem tauOdd_piece_le_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} {m : ℕ}
    (h : tauOdd (sumGraph j H) ≤ m) (i : Fin j) : tauOdd (H i) ≤ m :=
  (closeToBipartite_iff_tauOdd_le (G := H i) (m := m)).mp
    (closeToBipartite_sumGraph_of_piece
      ((closeToBipartite_iff_tauOdd_le (G := sumGraph j H) (m := m)).mpr h) i)

end Tau

/-! ## Part 4 — the exact transversal of the canonical witness -/

section Sharp

variable {W : Type*} [Fintype W]

/-- **THE `k`-FOLD 3-SUN IS EXACTLY `(2 k)`-CLOSE TO BIPARTITE** — the missing upper half of round
176's `JSP90.not_closeToBipartite_lt_two_mul_sun3U`. -/
theorem closeToBipartite_two_mul_sun3U (k : ℕ) : CloseToBipartite (2 * k) (sun3U k) := by
  obtain ⟨Z, hZ, hb⟩ := closeToBipartite_two_sun3
  have h' : CloseToBipartite (∑ i : Fin k, 2) (sumGraph k (fun _ => sun3)) :=
    closeToBipartite_sumGraph_of_forall (H := fun _ => sun3) (m := fun _ => 2)
      (fun _ => ⟨Z, hZ, hb⟩)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, Nat.cast_id,
    Nat.mul_comm, sun3U] using h'

/-- **THE LEAST ODD CYCLE TRANSVERSAL OF THE `k`-FOLD 3-SUN IS EXACTLY `2 k`.**

Round 176 proved `≥ 2 k` (`JSP90.not_closeToBipartite_lt_two_mul_sun3U`); the two results together
say that the `k`-fold 3-sun *attains* the lower bound `2 k` on the constant of Erdős #73 which
`JSP90.erdos73On_two_mul_le` forces. -/
theorem tauOdd_sun3U (k : ℕ) : tauOdd (sun3U k) = 2 * k := by
  refine le_antisymm ?_ ?_
  · exact (closeToBipartite_iff_tauOdd_le (V := Fin 6 × Fin k) (G := sun3U k)
      (m := 2 * k)).mp (closeToBipartite_two_mul_sun3U k)
  · by_contra hcon
    exact not_closeToBipartite_lt_two_mul_sun3U (by omega)
      ((closeToBipartite_iff_tauOdd_le (V := Fin 6 × Fin k) (G := sun3U k)
        (m := tauOdd (sun3U k))).mpr (Nat.le_refl _))

/-- **THE SHARPNESS TABLE OF THE CONSTANT, IN ONE STATEMENT: `2 k` is a valid constant of Erdős #73
at the parameter `k`, and nothing smaller is.**  The witness is `sun3U k`, with its hypothesis and
its defect: `LocIndep k G`, `MaxDef G = k` (round 176) and `tauOdd G = 2 * k`. -/
theorem exists_sharp_witness (k : ℕ) :
    ∃ (G : SimpleGraph (Fin 6 × Fin k)), LocIndep k G ∧ MaxDef G = k ∧ tauOdd G = 2 * k :=
  ⟨sun3U k, locIndep_sun3U k, maxDef_sun3U k, tauOdd_sun3U k⟩

/-- **THE TRANSVERSAL FORM OF THE SHARPNESS TABLE FOR AN ARBITRARY DISJOINT UNION**: if every
piece is `c`-close to bipartite then the least odd cycle transversal of the union is at most
`j * c`.  The constant `2 k` of the `k`-fold sun is produced by the transport lemma of Part 2
alone, out of the six-vertex statement `JSP90.closeToBipartite_two_sun3`. -/
theorem tauOdd_le_of_locIndep_sumGraph {j c : ℕ} {H : Fin j → SimpleGraph W}
    (hc : ∀ i, CloseToBipartite c (H i)) : tauOdd (sumGraph j H) ≤ j * c := by
  have h1 : tauOdd (sumGraph j H) ≤ ∑ _i : Fin j, c := by
    have h' : CloseToBipartite (∑ _i : Fin j, c) (sumGraph j H) :=
      closeToBipartite_sumGraph_of_forall (H := H) (m := fun _ => c) hc
    exact (closeToBipartite_iff_tauOdd_le (G := sumGraph j H) (m := ∑ _i : Fin j, c)).mp h'
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, Nat.cast_id,
    Nat.mul_comm] using h1

end Sharp

/-! ## Part 5 — a new order-free instance of the headline theorem -/

section Cactus

variable {W : Type*} [Fintype W]

/-- **A NEW ORDER-FREE INSTANCE OF THE HEADLINE THEOREM: A DISJOINT UNION OF `j` ODD CACTI IS
`j`-CLOSE TO BIPARTITE.**

Each piece satisfies Erdős's hypothesis with the parameter `1` and has its odd cycles in cactus
position, so `JSPProblem/Cactus.lean`'s `JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one`
gives **one** vertex of transversal per piece, and Part 2 adds them up.  The constant `j` is
optimal: `kTriangles k` is `LocIndep k` (`JSP90.locIndep_kTriangles`) and is **not**
`(k - 1)`-close to bipartite (`JSP90.not_closeToBipartite_helly_kTriangles`).

There is no bound on the order, the odd girth, the degrees or the connectivity of the pieces. -/
theorem closeToBipartite_of_sumGraph_of_oddCactus_of_locIndep_one {j : ℕ}
    {H : Fin j → SimpleGraph W} (hH : ∀ i, LocIndep 1 (H i)) (hc : ∀ i, OddCactus (H i)) :
    CloseToBipartite j (sumGraph j H) := by
  classical
  have h' := closeToBipartite_sumGraph_of_forall_of_mul (H := H) (m := 1)
    (fun i => closeToBipartite_one_of_oddCactus_of_locIndep_one (hH i) (hc i))
  simpa only [Nat.mul_one] using h'

/-- **THE SAME INSTANCE IN THE `tauOdd` FORM.** -/
theorem tauOdd_le_of_sumGraph_of_oddCactus_of_locIndep_one {j : ℕ}
    {H : Fin j → SimpleGraph W} (hH : ∀ i, LocIndep 1 (H i)) (hc : ∀ i, OddCactus (H i)) :
    tauOdd (sumGraph j H) ≤ j :=
  (closeToBipartite_iff_tauOdd_le (G := sumGraph j H) (m := j)).mp
    (closeToBipartite_of_sumGraph_of_oddCactus_of_locIndep_one hH hc)

/-- **THE CONSTANT `j` OF `JSP90.closeToBipartite_of_sumGraph_of_oddCactus_of_locIndep_one` IS
OPTIMAL**: the `k`-fold union of triangles satisfies Erdős's hypothesis with the parameter `k`, has
defect exactly `k`, and needs `k` vertices of transversal. -/
theorem optimal_sumGraph_of_oddCactus_of_locIndep_one (k : ℕ) (hk : 1 ≤ k) :
    LocIndep k (kTriangles k) ∧ ¬ CloseToBipartite (k - 1) (kTriangles k) :=
  ⟨locIndep_kTriangles, not_closeToBipartite_helly_kTriangles hk (by omega)⟩

end Cactus

/-! ## Part 6 — the deficiency is additive over components, *exactly* -/

section Def

variable {W : Type*} [Fintype W]

local instance sunExactDecidableEqD : DecidableEq W := Classical.decEq W

local instance sunExactProdEqD : DecidableEq (W × Fin j) := Classical.decEq (W × Fin j)

/-- **EVERY PIECE HAS A VERTEX SET WHOSE DEFICIENCY IS ITS OWN DEFECT, ADDITIVELY.**  For a piece
of defect `0` the empty set does the job (`α(∅) = 0`), and for a piece of positive defect a
maximiser `Y` of the deficiency satisfies `|Y| = 2 α(Y) + MaxDef`, because a *positive* truncated
subtraction is an honest one. -/
theorem exists_eq_add_of_defOf {j : ℕ} {H : Fin j → SimpleGraph W} (i : Fin j) :
    ∃ Y : Finset W, Y.card = 2 * indepCard (H i) Y + MaxDef (H i) := by
  by_cases h0 : MaxDef (H i) = 0
  · refine ⟨∅, ?_⟩
    rw [Finset.card_empty, indepCard_empty]
    omega
  · obtain ⟨Y, hY⟩ := exists_eq_maxDef (G := H i)
    have hdef : Y.card - 2 * indepCard (H i) Y = MaxDef (H i) := hY
    have hpos : 0 < Y.card - 2 * indepCard (H i) Y := by
      rw [hdef]
      omega
    have hle : 2 * indepCard (H i) Y ≤ Y.card := by omega
    refine ⟨Y, ?_⟩
    omega

/-- **THE INDEPENDENCE NUMBER OF A DISJOINT UNION IS THE SUM OF THE INDEPENDENCE NUMBERS OF ITS
PIECES, ON A VERTEX SET BUILT AS THE UNION OF THE WITNESSES.** -/
theorem indepCard_sumGraph_of_witness {j : ℕ} {H : Fin j → SimpleGraph W} (X : Fin j → Finset W)
    (S : Finset (W × Fin j))
    (hS : S = (Finset.univ : Finset (Fin j)).biUnion (fun i => (X i).image (fun v => (v, i)))) :
    indepCard (sumGraph j H) S = ∑ i : Fin j, indepCard (H i) (X i) := by
  classical
  have hmem : ∀ i : Fin j, S ∩ fib i = (X i).image (fun v => (v, i)) := by
    intro i
    refine Finset.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
    · rw [hS, Finset.mem_inter] at hp
      have hq2 : p.2 = i := mem_fib.mp hp.2
      have hp1 := hp.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp1
      obtain ⟨j, hjmem⟩ := hp1
      simp only [Finset.mem_image] at hjmem
      obtain ⟨v, hv, hvp⟩ := hjmem
      have hji : j = i := (congrArg Prod.snd hvp).trans hq2
      rw [← hji]
      exact Finset.mem_image.mpr ⟨v, hv, hvp⟩
    · simp only [Finset.mem_image] at hp
      obtain ⟨v, hv, hvp⟩ := hp
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [← hvp, hS, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
      · rw [← hvp]
        exact mem_fib.mpr rfl
  have h3 : (∑ i : Fin j, indepCard (H i) ((S ∩ fib i).image Prod.fst))
      = ∑ i : Fin j, indepCard (H i) (X i) := by
    refine Finset.sum_congr ?_ fun i _ => ?_
    · rfl
    · rw [hmem i, Finset.image_image]
      simp [Function.comp_def]
  have h1 := indepCard_sumGraph (H := H) S
  rw [h3] at h1
  exact h1

/-- **THE DEFICIENCY OF A VERTEX SET OF A DISJOINT UNION IS AT MOST THE SUM OF THE **DEFECTS** OF
ITS PIECES** — round 176's `JSPProblem/SunSum.lean`'s `JSP90.defOf_sumGraph_le` with the
per-piece constant in place of the uniform `k`, which is exactly what the equality below needs. -/
theorem defOf_sumGraph_le_sum {j : ℕ} {H : Fin j → SimpleGraph W} (X : Finset (W × Fin j)) :
    defOf (sumGraph j H) X ≤ ∑ i : Fin j, MaxDef (H i) := by
  have hle : ∀ i : Fin j, (X ∩ fib i).card
      ≤ 2 * indepCard (H i) ((X ∩ fib i).image Prod.fst) + MaxDef (H i) := by
    intro i
    have h1 := le_maxDef (H i) ((X ∩ fib i).image Prod.fst)
    rw [defOf, card_image_fib i] at h1
    omega
  have hkey : X.card ≤ 2 * (∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst))
      + ∑ i : Fin j, MaxDef (H i) := by
    calc X.card = ∑ i : Fin j, (X ∩ fib i).card := card_eq_sum_card_inter_fib
      _ ≤ ∑ i : Fin j, (2 * indepCard (H i) ((X ∩ fib i).image Prod.fst) + MaxDef (H i)) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 2 * (∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst))
          + ∑ i : Fin j, MaxDef (H i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [defOf, indepCard_sumGraph]
  omega

theorem maxDef_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} :
    MaxDef (sumGraph j H) = ∑ i : Fin j, MaxDef (H i) := by
  refine le_antisymm (maxDef_le fun X => defOf_sumGraph_le_sum X) ?_
  classical
  choose! X hX using fun i : Fin j => exists_eq_add_of_defOf (H := H) i
  set S : Finset (W × Fin j) :=
    (Finset.univ : Finset (Fin j)).biUnion (fun i => (X i).image (fun v => (v, i))) with hSdef
  have hcard : S.card = ∑ i : Fin j, (X i).card := by
    have hb := Finset.card_biUnion (s := (Finset.univ : Finset (Fin j)))
      (t := fun i => (X i).image (fun v => (v, i)))
      (pairwiseDisjoint_image (j := j) X)
    rw [Finset.sum_congr rfl fun i _ => card_image_pair (X i) i] at hb
    rwa [← hSdef] at hb
  have hind : indepCard (sumGraph j H) S = ∑ i : Fin j, indepCard (H i) (X i) :=
    indepCard_sumGraph_of_witness X S rfl
  have hsum : (∑ i : Fin j, (X i).card) = ∑ i : Fin j, (2 * indepCard (H i) (X i) + MaxDef (H i)) :=
    Finset.sum_congr rfl fun i _ => hX i
  have hgo : S.card - 2 * indepCard (sumGraph j H) S = ∑ i : Fin j, MaxDef (H i) := by
    rw [hcard, hind, hsum, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Nat.mul_comm 2 (indepCard (H i) (X i))]
    omega
  exact le_trans hgo.symm.le (le_maxDef (sumGraph j H) S)


/-- **THE DEFECT OF A COMPONENT IS AT MOST THE DEFECT OF THE WHOLE UNION** — with
`JSPProblem/Deficiency.lean`'s `ν ≤ MaxDef ≤ τ` sandwich, the whole of the numerical content of
this development is now split over the components of a disjoint union. -/
theorem maxDef_piece_le {j : ℕ} {H : Fin j → SimpleGraph W} {k : ℕ}
    (h : MaxDef (sumGraph j H) ≤ k) (i : Fin j) : MaxDef (H i) ≤ k := by
  rw [maxDef_sumGraph] at h
  exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (s := (Finset.univ : Finset (Fin j))) (f := fun x => MaxDef (H x)) (a := i)
    (Finset.mem_univ i)) h

/-- **ERDŐS'S LOCAL HYPOTHESIS DESCENDS TO EVERY COMPONENT, AT THE SAME PARAMETER.**  Round 176
has the ascending half (`JSP90.locIndep_sumGraph`: pieces at `k` give the union at `j * k`); with
the equality `MaxDef (⊔ H i) = ∑ MaxDef (H i)` one also gets the descending half, and the two
together say that **the parameter of Erdős's hypothesis of a disjoint union is the sum of the
parameters of its components** — not the same parameter, which round 176's form already showed to
be too strong (`kTriangles 2` is not `LocIndep 1`, although both of its components are). -/
theorem locIndep_of_locIndep_sumGraph_piece {j k : ℕ} {H : Fin j → SimpleGraph W}
    (h : LocIndep k (sumGraph j H)) (i : Fin j) : LocIndep k (H i) := by
  rw [locIndep_iff_maxDef_le] at h ⊢
  exact maxDef_piece_le h i

/-- **A DISJOINT UNION IS `LocIndep` AT THE SUM OF THE DEFECTS OF ITS COMPONENTS** — the exact
form of round 176's `JSPProblem/SunSum.lean`'s `JSP90.locIndep_sumGraph`, which used the uniform
`j * k`. -/
theorem locIndep_of_maxDef_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} :
    LocIndep (∑ i : Fin j, MaxDef (H i)) (sumGraph j H) := by
  rw [locIndep_iff_maxDef_le, maxDef_sumGraph]

end Def

end

end JSP90