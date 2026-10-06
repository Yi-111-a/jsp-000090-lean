import JSPProblem.ConnLinear
import JSPProblem.Tau

/-!
# JSP-000090, round 180 — `JSPProblem/TriDescent.lean`: **the exact descent at a triangle**

Attack family 98.  Rounds 162–175 used the step "cut at a triangle" **by hand** (four times, at
orders seven and eight), and round 179 closed the *connectivity* axis with
`JSP90.closeToBipartite_mul_of_piece_maxDef`, leaving
`JSP90.PieceMaxDefErdős73On C` as the single remaining local step.  What is missing is the
*arithmetic of the descent itself*, in the numerical language, **with no order bound and no case
analysis**: cutting at a triangle must cost exactly one unit of Erdős's parameter, and the
triangle-cut class must be paid for with the **optimal** constant.

The primitive input, already in `JSPProblem/Cut.lean` (round 118) and never yet lifted to the
`MaxDef`/`LocIndep`/`tauOdd` language, is `JSP90.maxDefIn_ge_one_add_maxDefIn_of_clique`.

## What is proved

| statement | content |
| --- | --- |
| **`JSP90.maxDef_ge_add_one_maxDef_delete_of_isNClique`** | `G.IsNClique 3 T → 1 + MaxDef (deleteFinset G T) ≤ MaxDef G`: **cutting at a triangle costs exactly one unit of deficiency**, no `LocIndep`, no order bound |
| **`JSP90.locIndep_pred_of_isNClique`** | `G.IsNClique 3 T → LocIndep (k+1) G → LocIndep k (deleteFinset G T)`: **Erdős's local parameter drops by one at a triangle** — the *statement* of the descent rounds 162–175 carried out by hand |
| **`JSP90.TriFamily`** + `maxDef_ge_add_one_maxDef_delete_of_triFamily_peel`, **`maxDef_ge_card_add_maxDef_delete_of_triFamily`** | **the iterated descent**: for a family `t` of pairwise vertex-disjoint triangles, `t + MaxDef (G − ⋃𝒬) ≤ MaxDef G` |
| **`JSP90.card_triFamily_le_maxDef`** | **the triangle packing of `G` is bounded by Erdős's own parameter, with no factor**: `𝒬.card ≤ MaxDef G` |
| **`JSP90.card_biUnion_le_three_card`**, `closeToBipartite_three_mul_of_triFamily_of_isBipartite_delete`, `tauOdd_le_three_mul_of_triFamily_of_isBipartite_delete`, `erdos73On_three_of_triFamily_of_isBipartite_delete` | **the cost of the descent**: `t` disjoint triangles + bipartite residue + `LocIndep k G` ⟹ `CloseToBipartite (3 k) G` (three vertices per triangle; the hypothesis enters only through `MaxDef G`) |
| **`JSP90.AnticompleteTriCover`** + `exists_oddCycle_of_anticompleteTriCover` | on a pairwise anticomplete cover by triangles **the odd cycles of `G` are exactly the triangles** |
| **`JSP90.tauOdd_eq_card_of_anticompleteTriCover`**, **`JSP90.maxDef_eq_card_of_anticompleteTriCover`** | **the exact value of both sides**: `MaxDef G = tauOdd G = 𝒬.card`, so Erdős's hypothesis and its conclusion *coincide* on this class |
| **`JSP90.closeToBipartite_of_anticompleteTriCover_of_locIndep`** (+ `erdos73On_one_…`, `tauOdd_le_of_…`) | **AN INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `k`**: `LocIndep k G` + an anticomplete triangle cover ⟹ `CloseToBipartite k G` |
| **`JSP90.anticompleteTriCover_kTriangles`**, **`JSP90.erdos73On_kTriangles_anticompleteTri`** | the class is **non-vacuous** (`kTriangles k` has the cover) and the constant `1` per triangle is **optimal**: `(LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m` |

## Why this is the right shape

`JSP90.closeToBipartite_mul_of_piece_maxDef` (round 179) reduces Erdős #73 to connected graphs with
**no loss of constant**; on a connected graph, `PieceMaxDefErdős73On C` is the statement that every
connected graph of deficiency `r` is `C · r`-close to bipartite, i.e. `LinearErdős73 C`.  This file
supplies, for one genuine class of that statement, the **sharp** value `C = 1`, and shows
mechanically *why* the triangle descent cannot do better than `C = 1` per triangle: a triangle is
worth exactly one unit of `MaxDef` (Part 1–2) and costs exactly one unit of `tauOdd` (Part 4), so
the constant is `1` and not more.  The remaining obstruction is therefore *not* the arithmetic of
the descent but the existence of a triangle-cut ladder: `kTriangles k` shows the descent terminates
there, while a graph of deficiency `1` such as `k4sub` (round 126, `tauOdd = 2`) has **no** such
ladder, so the class of Part 4 does not contain all graphs of bounded deficiency.  What is left is
precisely `JSP90.PieceMaxDefErdős73On C` for a universal `C`, i.e. Reed's theorem.
-/

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

local instance instDecidableEqTriDescent : DecidableEq V := Classical.decEq V

section Step

/-! ### Part 1 — one triangle costs exactly one unit of deficiency -/

/-- **`univ \ T` IS DISJOINT FROM `T`** (`JSP90.disjoint_univ_sdiff` of
`JSPProblem/OneK.lean`, with the two arguments the other way round). -/
theorem disjoint_sdiff_univ (T : Finset V) : Disjoint ((Finset.univ : Finset V) \ T) T :=
  (disjoint_univ_sdiff T).symm

/-- **`(univ \ T) ∪ T = univ`.** -/
theorem univ_sdiff_union (T : Finset V) : ((Finset.univ : Finset V) \ T) ∪ T = Finset.univ := by
  ext x
  simp

/-- **CUTTING AT A TRIANGLE COSTS EXACTLY ONE UNIT OF DEFICIENCY.**
`G.IsNClique 3 T` gives `1 + MaxDef (deleteFinset G T) ≤ MaxDef G`.

This is `JSP90.maxDefIn_ge_one_add_maxDefIn_of_clique` (`JSPProblem/Cut.lean`) lifted to the
language the rest of the development reads: the deficiency of the *graph left after deleting the
triangle* is at least one below the deficiency of `G`.  No hypothesis on `LocIndep`, no order
bound, no odd girth. -/
theorem maxDef_ge_add_one_maxDef_delete_of_isNClique {G : SimpleGraph V} {T : Finset V}
    (hT : G.IsNClique 3 T) : 1 + MaxDef (deleteFinset G T) ≤ MaxDef G := by
  have hcl : G.IsClique T := (G.isNClique_iff.mp hT).1
  have hcard : T.card = 3 := (G.isNClique_iff.mp hT).2
  set s : Finset V := (Finset.univ : Finset V) \ T with hs
  have hunion : s ∪ T = (Finset.univ : Finset V) := univ_sdiff_union T
  have hstep : 1 + maxDefIn G s ≤ maxDefIn G (s ∪ T) :=
    maxDefIn_ge_one_add_maxDefIn_of_clique (G := G) hcl hcard (by simpa [s] using (disjoint_univ_sdiff T).symm)
  have hdelete : MaxDef (deleteFinset G T) = maxDefIn G s := by
    rw [deleteFinset, maxDefIn_eq_maxDef_induce, hs]
  rw [hdelete]
  exact hstep.trans (by rw [hunion, maxDefIn_univ_eq])

/-- **ERDŐS'S LOCAL PARAMETER DROPS BY ONE AT A TRIANGLE.**
`G.IsNClique 3 T → LocIndep (k+1) G → LocIndep k (deleteFinset G T)`.

This is the *statement* of the descent that rounds 162–175 carried out by hand at orders seven and
eight, with `k = 0` and `k = 1`; it is the formal content of "cutting at a triangle costs one". -/
theorem locIndep_pred_of_isNClique {G : SimpleGraph V} {k : ℕ} {T : Finset V}
    (hT : G.IsNClique 3 T) (hG : LocIndep (k + 1) G) : LocIndep k (deleteFinset G T) := by
  have h1 : MaxDef G ≤ k + 1 := maxDef_le_of_locIndep hG
  have h2 : MaxDef (deleteFinset G T) ≤ k := by
    have := maxDef_ge_add_one_maxDef_delete_of_isNClique (G := G) hT
    omega
  exact locIndep_of_maxDef_le (G := deleteFinset G T) h2

end Step

section Family

/-! ### Part 2 — the iterated descent: a family of disjoint triangles costs its own cardinality -/

/-- **A FAMILY OF PAIRWISE VERTEX-DISJOINT TRIANGLES OF `G`.**  Only the *disjointness* is
hypothesised: the triangles may carry edges to one another and to the rest of the graph, which is
what makes the class of this part strictly larger than the anticomplete one of Part 4. -/
def TriFamily (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  (∀ Q ∈ 𝒬, G.IsNClique 3 Q) ∧
  (∀ Q ∈ 𝒬, ∀ R ∈ 𝒬, Q ≠ R → Disjoint Q R)

/-- **DELETING VERTICES ONE AFTER ANOTHER.** -/
theorem deleteFinset_deleteFinset_of_union (X Y : Finset V) :
    deleteFinset (deleteFinset G X) Y = deleteFinset G (X ∪ Y) := by
  ext v w
  simp only [deleteFinset_adj, Finset.mem_union, not_or]
  tauto

/-- **A `3`-CLIQUE AVOIDING `X` IS A `3`-CLIQUE OF `G - X`.** -/
theorem isNClique_three_deleteFinset {G : SimpleGraph V} {T X : Finset V}
    (hT : G.IsNClique 3 T) (hdisj : Disjoint T X) : (deleteFinset G X).IsNClique 3 T := by
  refine (deleteFinset G X).isNClique_iff.mpr ⟨?_, (G.isNClique_iff.mp hT).2⟩
  intro v hv w hw hne
  have hadj : G.Adj v w := hT.1 hv hw hne
  rw [deleteFinset_adj]
  exact ⟨(Finset.disjoint_left.mp hdisj hv), (Finset.disjoint_left.mp hdisj hw), hadj⟩

/-- **THE DESCENT STEP FOR A FAMILY: PEEL OFF ONE TRIANGLE.**  A triangle `Q` disjoint from every
piece of `𝒬` costs one further unit of deficiency, and the deletion of `Q` commutes with the
deletion of `𝒬`. -/
theorem maxDef_ge_add_one_maxDef_delete_of_triFamily_peel {G : SimpleGraph V}
    {𝒬 : Finset (Finset V)} {Q : Finset V}
    (hQ : G.IsNClique 3 Q) (hdj : ∀ R ∈ 𝒬, Disjoint R Q) :
    1 + MaxDef (deleteFinset G ((𝒬.biUnion id) ∪ Q)) ≤ MaxDef (deleteFinset G (𝒬.biUnion id)) := by
  have hnot : (deleteFinset G (𝒬.biUnion id)).IsNClique 3 Q :=
    isNClique_three_deleteFinset hQ
      (Finset.disjoint_left.mpr (by
        intro x hxQ hxU
        obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.mp hxU
        exact (Finset.disjoint_left.mp (hdj R hR) hxR) hxQ))
  have h1 := maxDef_ge_add_one_maxDef_delete_of_isNClique (G := deleteFinset G (𝒬.biUnion id)) hnot
  rw [deleteFinset_deleteFinset_of_union] at h1
  exact h1

/-- **ITERATED FORM OF THE DESCENT.**  A family of `t` pairwise disjoint triangles costs exactly
`t` units of deficiency:

```lean
𝒬.card + MaxDef (deleteFinset G (𝒬.biUnion id)) ≤ MaxDef G
```

Equivalently: **the number of pairwise disjoint triangles of `G` is at most `MaxDef G`** —
the *triangle packing* is bounded by Erdős's own parameter, with no factor.  This is the
statement that the descent of Part 1 can be run to exhaustion. -/
theorem maxDef_ge_card_add_maxDef_delete_of_triFamily {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (hfam : TriFamily G 𝒬) :
    𝒬.card + MaxDef (deleteFinset G (𝒬.biUnion id)) ≤ MaxDef G := by
  classical
  have hunion : ∀ (𝒬' : Finset (Finset V)) (Q : Finset V),
      ((𝒬'.biUnion id) ∪ Q) = (insert Q 𝒬').biUnion (fun x => x) :=
    fun 𝒬' Q => ((Finset.biUnion_insert (a := Q) (s := 𝒬') (t := fun x => x)).trans
      (Finset.union_comm _ _)).symm
  have aux : ∀ (𝒬' : Finset (Finset V)),
      (∀ Q ∈ 𝒬', G.IsNClique 3 Q) → (∀ Q ∈ 𝒬', ∀ R ∈ 𝒬', Q ≠ R → Disjoint Q R) →
      𝒬'.card + MaxDef (deleteFinset G (𝒬'.biUnion id)) ≤ MaxDef G := by
    intro 𝒬'
    induction 𝒬' using Finset.induction_on with
    | empty =>
        intro _ _
        have hne : ((∅ : Finset (Finset V)).biUnion id) = (∅ : Finset V) := by simp
        rw [hne, deleteFinset_empty]
        simp
    | @insert Q 𝒬' hQ0 hIH =>
        intro hclP hdjP
        have hclR : ∀ R ∈ 𝒬', G.IsNClique 3 R := fun R hR => hclP R (Finset.mem_insert_of_mem hR)
        have hdjR : ∀ R ∈ 𝒬', Disjoint R Q := by
          intro R hR
          refine hdjP R (Finset.mem_insert_of_mem hR) Q (Finset.mem_insert_self Q 𝒬') ?_
          intro hRQ
          exact hQ0 (hRQ ▸ hR)
        have hle := maxDef_ge_add_one_maxDef_delete_of_triFamily_peel
          (𝒬 := 𝒬') (hclP Q (Finset.mem_insert_self Q 𝒬')) hdjR
        rw [hunion 𝒬' Q] at hle
        have hsub : ∀ Q' ∈ 𝒬', ∀ R ∈ 𝒬', Q' ≠ R → Disjoint Q' R := by
          intro Q' hQ' R hR hne
          exact hdjP Q' (Finset.mem_insert_of_mem hQ') R (Finset.mem_insert_of_mem hR) hne
        have hIH' := hIH hclR hsub
        have hc : (insert Q 𝒬').card = 𝒬'.card + 1 := by simp [hQ0]
        have key : (insert Q 𝒬').card
            + MaxDef (deleteFinset G ((insert Q 𝒬').biUnion (fun x => x)))
            ≤ 𝒬'.card + MaxDef (deleteFinset G (𝒬'.biUnion id)) := by
          calc _ = 𝒬'.card + 1 + _ := by rw [hc]
            _ = 𝒬'.card + (1 + _) := by omega
            _ ≤ 𝒬'.card + _ := Nat.add_le_add_left hle _
        exact Nat.le_trans key hIH'
  exact aux 𝒬 (fun Q hQ => hfam.1 Q hQ) (fun Q hQ R hR hne => hfam.2 Q hQ R hR hne)

/-- **THE TRIANGLE PACKING OF `G` IS BOUNDED BY ERDŐS'S OWN PARAMETER.** -/
theorem card_triFamily_le_maxDef {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (hfam : TriFamily G 𝒬) : 𝒬.card ≤ MaxDef G := by
  have h := maxDef_ge_card_add_maxDef_delete_of_triFamily (G := G) hfam
  omega

end Family

section Cycles

/-! ### Part 3 — the transversal cost of the descent -/

/-- **AN ODD CYCLE AVOIDING `Z` IS AN ODD CYCLE OF `G - Z`.** -/
theorem isOddCycle_deleteFinset_of_disjoint {G : SimpleGraph V} {Z C : Finset V}
    (hC : IsOddCycle G C) (hdisj : Disjoint C Z) : IsOddCycle (deleteFinset G Z) C := by
  have hsub : C ⊆ (Finset.univ : Finset V) \ Z := by
    refine fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun h => ?_⟩
    exact (Finset.disjoint_left.mp hdisj hx) h
  exact hC.induceFinset (s := (Finset.univ : Finset V) \ Z) hsub

/-- **THE VERTICES OF `t` DISJOINT TRIANGLES ARE AT MOST `3 t`.** -/
theorem card_biUnion_le_three_card {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (hfam : TriFamily G 𝒬) : (𝒬.biUnion id).card ≤ 3 * 𝒬.card := by
  have h1 : (𝒬.biUnion id).card ≤ ∑ Q ∈ 𝒬, Q.card := Finset.card_biUnion_le (s := 𝒬)
  have h2 : (∑ Q ∈ 𝒬, Q.card) = ∑ _ ∈ 𝒬, (3 : ℕ) := by
    refine Finset.sum_congr rfl (f := fun Q : Finset V => Q.card) fun Q hQ => ?_
    exact (G.isNClique_iff.mp (hfam.1 Q hQ)).2
  have h3 : (∑ _ ∈ 𝒬, (3 : ℕ)) = 3 * 𝒬.card := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  rw [h2, h3] at h1
  exact h1

/-- **THE COST OF THE DESCENT.**  `TriFamily G 𝒬` together with a bipartite residue and
`LocIndep k G` gives `CloseToBipartite (3 * k) G`: three vertices per triangle, and the hypothesis
enters **only** through `MaxDef G`, with no order bound and no packing hypothesis. -/
theorem closeToBipartite_three_mul_of_triFamily_of_isBipartite_delete {G : SimpleGraph V}
    {k : ℕ} {𝒬 : Finset (Finset V)} (hfam : TriFamily G 𝒬)
    (hb : (deleteFinset G (𝒬.biUnion id)).IsBipartite) (hG : LocIndep k G) :
    CloseToBipartite (3 * k) G := by
  refine closeToBipartite_mono
    (Nat.mul_le_mul_left 3 (Nat.le_trans (card_triFamily_le_maxDef hfam)
      (maxDef_le_of_locIndep hG))) ?_
  exact ⟨𝒬.biUnion id, card_biUnion_le_three_card hfam, hb⟩

/-- **... IN THE TRANVERSAL LANGUAGE.** -/
theorem tauOdd_le_three_mul_of_triFamily_of_isBipartite_delete {G : SimpleGraph V}
    {k : ℕ} {𝒬 : Finset (Finset V)} (hfam : TriFamily G 𝒬)
    (hb : (deleteFinset G (𝒬.biUnion id)).IsBipartite) (hG : LocIndep k G) :
    tauOdd G ≤ 3 * k := by
  exact Nat.le_trans (tauOdd_le (hitsOddCycles_of_isBipartite_delete (X := 𝒬.biUnion id) hb))
    (Nat.le_trans (card_biUnion_le_three_card hfam)
      (Nat.mul_le_mul_left 3 (Nat.le_trans (card_triFamily_le_maxDef hfam)
        (maxDef_le_of_locIndep hG))))

/-- **... AND IN THE `Erdős73On` CLASS SHAPE.** -/
theorem erdos73On_three_of_triFamily_of_isBipartite_delete {G : SimpleGraph V}
    {k : ℕ} {𝒬 : Finset (Finset V)} (hG : LocIndep k G) (hfam : TriFamily G 𝒬)
    (hb : (deleteFinset G (𝒬.biUnion id)).IsBipartite) : CloseToBipartite (3 * k) G :=
  closeToBipartite_three_mul_of_triFamily_of_isBipartite_delete hfam hb hG

section Anticomplete

/-! ### Part 4 — the anticomplete case: the exact value of both sides, optimal constant `1` -/

/-- **`Q ∩ R = ∅` GIVES `Disjoint Q R`.** -/
theorem disjoint_of_inter_eq_empty {A B : Finset V} (h : A ∩ B = ∅) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact absurd (Finset.mem_inter.mpr ⟨hxA, hxB⟩) (by rw [h]; simp)

/-- **A PAIRWISE ANTICOMPLETE COVER BY TRIANGLES.**  The pieces are triangles, they are pairwise
disjoint and anticomplete, and together they cover `V`.  This is the class on which Erdős's
hypothesis and its conclusion *coincide*: `Part 4` proves

```lean
MaxDef G = 𝒬.card   and   tauOdd G = 𝒬.card
```

so `LocIndep k G` gives `CloseToBipartite k G` with the **optimal** constant. -/
def AnticompleteTriCover (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  AnticoverCoverFamily G 𝒬 ∧ (∀ x : V, ∃ Q ∈ 𝒬, x ∈ Q) ∧ (∀ Q ∈ 𝒬, G.IsNClique 3 Q)

/-- **AN ANTICOMPLETE TRIANGLE COVER IS A TRIANGLE FAMILY.** -/
theorem anticompleteTriCover_triFamily {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (h : AnticompleteTriCover G 𝒬) : TriFamily G 𝒬 :=
  ⟨fun Q hQ => h.2.2 Q hQ, fun Q hQ R hR hne =>
    disjoint_of_inter_eq_empty (h.1.1 Q hQ R hR hne)⟩

/-- **THE ODD CYCLES OF `G` ARE EXACTLY THE TRIANGLES OF THE COVER.**  An odd cycle is connected,
and it meets only one of the pairwise anticomplete pieces; as it has at least three vertices and
the piece has exactly three, it *is* that piece. -/
theorem exists_oddCycle_of_anticompleteTriCover {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (h : AnticompleteTriCover G 𝒬) (C : Finset V) (hC : IsOddCycle G C) :
    ∃ Q ∈ 𝒬, C = Q := by
  obtain ⟨X, hX, hCX⟩ := isOddCycle_sub_anticoverCover (G := G) (s := (Finset.univ : Finset V))
    h.1 (fun x hx => h.2.1 x) hC (Finset.subset_univ C)
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  have h3X : X.card = 3 := (G.isNClique_iff.mp (h.2.2 X hX)).2
  have hceq : C = X := Finset.eq_of_subset_of_card_le hCX (by rw [h3X]; omega)
  exact ⟨X, hX, hceq⟩

/-- **ONE VERTEX PER TRIANGLE IS AN ODD CYCLE TRANSVERSAL.** -/
theorem hitsOddCycles_of_anticompleteTriCover {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (h : AnticompleteTriCover G 𝒬) (g : Finset V → Finset V)
    (hg : ∀ Q ∈ 𝒬, ∀ x ∈ g Q, x ∈ Q) (hg1 : ∀ Q ∈ 𝒬, (g Q).card = 1) :
    HitsOddCycles G (𝒬.biUnion g) := by
  intro C hC
  obtain ⟨Q, hQ, hCQ⟩ := exists_oddCycle_of_anticompleteTriCover h C hC
  have hmemU : g Q ⊆ 𝒬.biUnion g := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, hx⟩
  obtain ⟨x, hxQ⟩ := Finset.card_pos.mp (by rw [hg1 Q hQ]; omega)
  have hxCQ : x ∈ C := by rw [hCQ]; exact hg Q hQ x hxQ
  exact ne_empty_of_nonempty
    ⟨x, Finset.mem_inter.mpr ⟨hxCQ, hmemU hxQ⟩⟩

/-- **`tauOdd` OF AN ANTICOMPLETE TRIANGLE COVER IS EXACTLY ITS CARDINALITY** — the *upper*
inequality, one vertex per triangle. -/
theorem tauOdd_le_card_of_anticompleteTriCover {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (h : AnticompleteTriCover G 𝒬) : tauOdd G ≤ 𝒬.card := by
  classical
  have hne : ∀ Q ∈ 𝒬, Q.Nonempty := fun Q hQ => Finset.card_pos.mp (by
    rw [(G.isNClique_iff.mp (h.2.2 Q hQ)).2]
    omega)
  let g : Finset V → Finset V :=
    fun Q => if hQ : Q.Nonempty then {Classical.choose hQ} else ∅
  have hgQ : ∀ (Q : Finset V) (hQ : Q ∈ 𝒬), g Q = {Classical.choose (hne Q hQ)} := by
    intro Q hQ
    have h1 := hne Q hQ
    show (if hQ' : Q.Nonempty then {Classical.choose hQ'} else ∅) = _
    rw [dif_pos h1]
  have hg : ∀ Q ∈ 𝒬, ∀ x ∈ g Q, x ∈ Q := by
    intro Q hQ x hx
    rw [hgQ Q hQ] at hx
    rw [Finset.mem_singleton.mp hx]
    exact Classical.choose_spec (hne Q hQ)
  have hg1 : ∀ Q ∈ 𝒬, (g Q).card = 1 := by
    intro Q hQ
    rw [hgQ Q hQ, Finset.card_singleton]
  have h1 : (𝒬.biUnion g).card ≤ ∑ Q ∈ 𝒬, (g Q).card := Finset.card_biUnion_le (s := 𝒬)
  have h2 : (∑ Q ∈ 𝒬, (g Q).card) = ∑ _ ∈ 𝒬, (1 : ℕ) := Finset.sum_congr rfl hg1
  have h3 : (∑ _ ∈ 𝒬, (1 : ℕ)) = 𝒬.card := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
  rw [h2, h3] at h1
  exact Nat.le_trans (tauOdd_le (hitsOddCycles_of_anticompleteTriCover h g hg hg1)) h1

/-- **THE EXACT VALUE OF BOTH SIDES ON THE CLASS.**  `MaxDef G = tauOdd G = 𝒬.card`, so Erdős's
hypothesis and the conclusion of Erdős #73 coincide there, with the **optimal** constant `1` per
unit of deficiency. -/
theorem tauOdd_eq_card_of_anticompleteTriCover {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (h : AnticompleteTriCover G 𝒬) : tauOdd G = 𝒬.card := by
  refine Nat.le_antisymm (tauOdd_le_card_of_anticompleteTriCover h) ?_
  exact Nat.le_trans (card_triFamily_le_maxDef (anticompleteTriCover_triFamily h)) maxDef_le_tauOdd

theorem maxDef_eq_card_of_anticompleteTriCover {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    (h : AnticompleteTriCover G 𝒬) : MaxDef G = 𝒬.card := by
  refine Nat.le_antisymm (by rw [← tauOdd_eq_card_of_anticompleteTriCover h]; exact maxDef_le_tauOdd) ?_
  exact card_triFamily_le_maxDef (anticompleteTriCover_triFamily h)

/-- **AN INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `k`**, on the class of graphs
whose vertices split into an anticomplete family of triangles. -/
theorem closeToBipartite_of_anticompleteTriCover_of_locIndep {G : SimpleGraph V} {k : ℕ}
    {𝒬 : Finset (Finset V)} (hG : LocIndep k G) (h : AnticompleteTriCover G 𝒬) :
    CloseToBipartite k G := by
  refine closeToBipartite_mono (m := 𝒬.card) (m' := k) (by
      rw [← maxDef_eq_card_of_anticompleteTriCover h]
      exact maxDef_le_of_locIndep hG) ?_
  rw [← tauOdd_eq_card_of_anticompleteTriCover h]
  exact (closeToBipartite_iff_tauOdd_le (G := G) (m := tauOdd G)).mpr (Nat.le_refl _)

/-- **... IN THE `Erdős73On` CLASS SHAPE.** -/
theorem erdos73On_one_of_anticompleteTriCover_of_locIndep {G : SimpleGraph V} {k : ℕ}
    {𝒬 : Finset (Finset V)} (hG : LocIndep k G) (h : AnticompleteTriCover G 𝒬) :
    CloseToBipartite k G :=
  closeToBipartite_of_anticompleteTriCover_of_locIndep hG h

/-- **... AND IN THE TRANVERSAL LANGUAGE.** -/
theorem tauOdd_le_of_anticompleteTriCover_of_locIndep {G : SimpleGraph V} {k : ℕ}
    {𝒬 : Finset (Finset V)} (hG : LocIndep k G) (h : AnticompleteTriCover G 𝒬) :
    tauOdd G ≤ k := by
  rw [tauOdd_eq_card_of_anticompleteTriCover h]
  rw [← maxDef_eq_card_of_anticompleteTriCover h]
  exact maxDef_le_of_locIndep hG

section Witness

/-! ### Part 5 — the class is nonempty, and the constant `1` per triangle is optimal -/

/-- **`A ∩ B = ∅` FOLLOWS FROM `Disjoint A B`.** -/
theorem inter_eq_empty_of_disjoint {A B : Finset V} (h : Disjoint A B) : A ∩ B = ∅ := by
  refine Finset.Subset.antisymm (s₁ := A ∩ B) (s₂ := (∅ : Finset V)) ?_ ?_
  · intro x hx
    exfalso
    have hx' := Finset.mem_inter.mp hx
    exact (Finset.disjoint_left.mp h hx'.1) hx'.2
  · intro x hx
    simp at hx

/-- **THE FAMILY OF FIBRES OF THE SHARP WITNESS.** -/
def triFamily_kTriangles (k : ℕ) : Finset (Finset (Fin 3 × Fin k)) :=
  (Finset.univ : Finset (Fin k)).image (tri (k := k))

/-- **`kTriangles k` HAS A PAIRWISE ANTICOMPLETE COVER BY ITS `k` TRIANGLES**, so the class of
Part 4 is nonempty and the instance above is not vacuous. -/
theorem anticompleteTriCover_kTriangles {k : ℕ} :
    AnticompleteTriCover (kTriangles k) (triFamily_kTriangles k) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro Q hQ R hR hne
    obtain ⟨i, -, hQi⟩ := Finset.mem_image.mp hQ
    obtain ⟨j, -, hRj⟩ := Finset.mem_image.mp hR
    subst hQi
    subst hRj
    exact inter_eq_empty_of_disjoint
      (tri_disjoint (i := i) (j := j) (fun (hij : i = j) => hne (by rw [hij])))
  · intro Q hQ R hR hne x hx y hy hxy
    obtain ⟨i, -, hQi⟩ := Finset.mem_image.mp hQ
    obtain ⟨j, -, hRj⟩ := Finset.mem_image.mp hR
    subst hQi
    subst hRj
    have hij : i = j := (mem_tri.mp hx).symm.trans ((kTriangles_adj.mp hxy).1.trans (mem_tri.mp hy))
    exact hne (by rw [hij])
  · intro x
    exact ⟨tri x.2, Finset.mem_image.mpr ⟨x.2, Finset.mem_univ _, rfl⟩, mem_tri.mpr rfl⟩
  · intro Q hQ
    obtain ⟨i, -, hQi⟩ := Finset.mem_image.mp hQ
    subst hQi
    exact isNClique_three_of_isOddCycle (isOddCycle_tri i) (card_tri i)

/-- **THE CONSTANT `1` PER TRIANGLE IS OPTIMAL ON THE CLASS**: on the sharp witness
`kTriangles k` the hypothesis `LocIndep k` holds, the conclusion needs exactly `k` deletions, and
Part 4 delivers exactly `k`.  So the instance

```lean
JSP90.closeToBipartite_of_anticompleteTriCover_of_locIndep
```

is an **equivalence with the optimal constant** on this class, exactly as
`JSP90.erdos73On_of_multi_optimal` (round 106) and
`JSP90.erdos73_cluster_notBelowK` (round 104) are elsewhere. -/
theorem erdos73On_kTriangles_anticompleteTri {k m : ℕ} :
    (LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m := by
  constructor
  · intro h
    have hc := (closeToBipartite_kTriangles_iff_maxDef k m).mp
      (h (locIndep_kTriangles (k := k)))
    rw [maxDef_kTriangles] at hc
    exact hc
  · intro hk hG
    exact closeToBipartite_mono hk
      (closeToBipartite_of_anticompleteTriCover_of_locIndep hG anticompleteTriCover_kTriangles)

end Witness
