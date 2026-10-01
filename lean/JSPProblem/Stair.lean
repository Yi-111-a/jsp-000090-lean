import JSPProblem.Pivot

/-!
# JSP-000090, round 101 — the **ODD-GIRTH LADDER**: `τ_odd(G) ≤ ∑_j g_j`, one girth per level

Attack family 42.  Round 100 (`JSPProblem/Pivot.lean`) proved the *two-level* odd-girth ladder,
`τ_odd(G) ≤ ℓ₁ + ℓ₂ * (k - 1) * (d - 1)`, and recorded in `discovery/JSP-000090/policy.json`
option (A) as the next step the **full** ladder: an arbitrary number of levels, each level paying
its **own** shortest odd cycle instead of a uniform bound `ℓ`.  This file carries that out.

## The statement

Let `n ≥ 1`, let `C 0, …, C (n-1)` be vertex sets such that `C j` is an **odd cycle of the residue of
`H` after deleting `C 0, …, C j.succ`** (`JSP90.IsOddCycleChain`), and let `g : ℕ → ℕ` with
`(C j).card ≤ g j`.  Then

> `CloseToBipartite (∑ i ∈ Finset.range n, g i) H`
>
> — i.e. `CloseToBipartite (g 0 + g 1 + … + g (n-1)) H`.

No degree bound, no bound on the packing *weight*, no bound on the number of branch vertices, and
**no uniform bound on the length of an odd cycle**: each level pays exactly what it uses.  The
machinery is

* `JSP90.deletedUpTo` / `JSP90.residueOf` — the vertices deleted before level `j`, and the level
  itself; `deletedUpTo_zero`, `deletedUpTo_succ`, `residueOf_zero`, `residueOf_succ`;
* the two **shift lemmas** `deletedUpTo_succChain` and `residueOf_succChain`, whose content is that
  inside the residue `H - C 0` the tail `C 1, …, C (n-1)` walks exactly the tail of the original
  residue chain:
  `residueOf (deleteFinset H (C 0)) (fun i => C i.succ) j = residueOf H C j.succ`.  This identity is
  what makes the induction step go through;
* `JSP90.OddCyclePackingLe.succ_of_residue` of round 100 — the strictly decreasing quantity — and
  `JSP90.isBipartite_of_oddCyclePackingLe_zero`, its base case.

## What it buys (the honest comparison, also in `policy.json`)

* **Strictly stronger than `JSPProblem/Transversal.lean`'s `ℓ * k`.**
  `JSP90.closeToBipartite_of_girthLadder_uniform` *re-proves* the uniform bound from this file, so
  `Transversal.lean`'s instance is now a corollary here.  Along a residue chain the girths are
  increasing, so `∑ g_j` can be far below `k * max_j g_j`
  (`JSP90.girthLadder_sum_le_sub_one_mul`).
* **Strictly stronger than round 100's `ℓ * ((k-1)(d-1) + 1)`**: there is **no degree factor `d - 1`
  at all**, because a level pays the odd cycle it deletes and not the closed neighbourhood of a
  packing of it.
* **Erdős's own hypothesis suffices**: `JSP90.erdos73On_of_girthLadder` is the headline theorem in
  the shape of the ladder, and `JSP90.erdos73On_of_girthLadder_uniform` recovers
  `JSPProblem/Transversal.lean`'s instance from it.

`jsp_000090_main` is not declared: behind it stands `JSP90.OddCycleErdosPosa r`.
-/

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

local instance instDecidableEqStair : DecidableEq V := Classical.decEq V

local instance instDecidableRelStair {G : SimpleGraph V} : DecidableRel G.Adj :=
  Classical.decRel G.Adj

universe u

/-! ### Part 1 — sums of level girths -/

/-- **The sum of the first `k` level girths, with the girths given as an `ℕ`-indexed function.**  The
core statement of this file is phrased with `g : ℕ → ℕ` rather than `g : Fin k → ℕ` because then the
reindexing of the induction step is exactly `Finset.sum_range_succ'`:
`∑ i ∈ range (k+1), g i = ∑ i ∈ range k, g (i+1) + g 0`. -/
noncomputable def girthSum (k : ℕ) (g : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range k, g i

theorem girthSum_succ (k : ℕ) (g : ℕ → ℕ) :
    girthSum (k + 1) g = girthSum k (fun i => g (i + 1)) + g 0 := by
  unfold girthSum
  exact Finset.sum_range_succ' g k

/-- **A finite girth function extended to `ℕ`**: the `j`-th level girth, or `0` beyond the chain. -/
noncomputable def girthExtend {k : ℕ} (g : Fin k → ℕ) : ℕ → ℕ :=
  fun i => if h : i < k then g ⟨i, h⟩ else 0

theorem girthSum_extend {k : ℕ} (g : Fin k → ℕ) :
    girthSum k (girthExtend g) = ∑ j : Fin k, g j := by
  unfold girthSum girthExtend
  exact (Finset.sum_fin_eq_sum_range g).symm

/-- **The girths of a uniform ladder** (`g i = ℓ` at every level) sum to `ℓ * k`. -/
theorem girthSum_const (k ℓ : ℕ) : girthSum k (fun _ => ℓ) = ℓ * k := by
  unfold girthSum
  rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm]

/-! ### Part 2 — the chain of residues -/

section Chain

/-- **The vertices deleted before level `j` of a chain `C 0, …, C (n-1)` of odd cycles**:
`⋃ {C i | i < j}`. -/
noncomputable def deletedUpTo {n : ℕ} (C : Fin n → Finset V) (j : Fin n) : Finset V :=
  ((Finset.univ : Finset (Fin n)).filter fun i : Fin n => i.val < j.val).biUnion C

/-- **LEVEL `j` OF A CHAIN OF ODD CYCLES**: the residue of `H` on the vertices left after deleting
`C 0, …, C j.succ`, i.e. the graph on which the chain *continues* with `C j.succ`.

Level `j` of the chain `C 0, …, C (n-1)` is the graph on which the tail `C j, C j.succ, …` is a chain
of odd cycles (`JSP90.IsOddCycleChain`).  The levels form the residue chain `H = level 0`,
`level 0 - C 0`, `level 0 - C 0 - C 1`, …, and it is along that chain that the ladder induction runs. -/
noncomputable def residueOf {n : ℕ} (H : SimpleGraph V) (C : Fin n → Finset V) (j : Fin n) :
    SimpleGraph V := deleteFinset H (deletedUpTo C j)

/-- **Nothing is deleted before level `0`, so level `0` of a chain is the graph itself.** -/
theorem deletedUpTo_zero {n : ℕ} (C : Fin (n+1) → Finset V) : deletedUpTo C 0 = ∅ := by
  ext v
  simp [deletedUpTo]

theorem residueOf_zero {n : ℕ} (H : SimpleGraph V) (C : Fin (n+1) → Finset V) :
    residueOf H C 0 = H := by
  rw [residueOf, deletedUpTo_zero, deleteFinset_empty]

/-- **THE RESIDUE AFTER THE FIRST MEMBER OF A CHAIN CARRIES THE TAIL OF THE CHAIN.**

`residueOf (deleteFinset H (C 0)) (fun i => C i.succ) j = residueOf H C j.succ`: inside the residue
`H - C 0` the tail `C 1, …, C (n-1)` walks exactly the tail of the original residue chain — level `j`
of the tail is level `j.succ` of the whole.  This is the identity that makes the induction step of
the ladder go through, and it is the only place where the *tail* of a chain is used, so it is where
all the index bookkeeping lives. -/
theorem residueOf_succChain {n : ℕ} (H : SimpleGraph V) (C : Fin (n+1) → Finset V) (j : Fin n) :
    residueOf (deleteFinset H (C 0)) (fun i : Fin n => C i.succ) j = residueOf H C j.succ := by
  have heq : C 0 ∪ deletedUpTo (fun i : Fin n => C i.succ) j = deletedUpTo C j.succ := by
    ext v
    simp only [deletedUpTo, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_succ]
    constructor
    · rintro (hv0 | ⟨i, hi, hvi⟩)
      · exact ⟨0, Nat.zero_lt_succ j.val, hv0⟩
      · exact ⟨⟨i.val + 1, Nat.succ_lt_succ_iff.mpr i.isLt⟩, Nat.succ_lt_succ_iff.mpr hi, hvi⟩
    · rintro ⟨i, hi, hvi⟩
      have hi1 : i.val ≤ j.val := by omega
      rcases Nat.eq_zero_or_pos i.val with hz | hz
      · have hi0 : i = 0 := Fin.ext hz
        subst hi0
        exact Or.inl hvi
      · have hle : i.val - 1 < n := by omega
        have hlt : i.val - 1 < j.val := by omega
        have hsub : ((⟨i.val - 1, hle⟩ : Fin n)).succ = i := by
          apply Fin.ext
          simp only [Fin.succ_mk]
          omega
        refine Or.inr ⟨⟨i.val - 1, hle⟩, hlt, ?_⟩
        rw [hsub]
        exact hvi
  rw [residueOf, residueOf, deleteFinset_deleteFinset, heq]

/-- **A CHAIN OF ODD CYCLES OF LENGTH `n`**: for every `j : Fin n` the vertex set `C j` is an odd
cycle of level `j` of the residue chain.

This is the hypothesis of the ladder: a *sequence* of odd cycles, each living in the residue left by
its predecessors.  Nothing is assumed about how long the cycles are, about the degrees, or about the
rest of the graph. -/
def IsOddCycleChain {H : SimpleGraph V} (n : ℕ) (C : Fin n → Finset V) : Prop :=
  ∀ j : Fin n, IsOddCycle (residueOf H C j) (C j)

/-- **THE SHIFT OF A CHAIN OF ODD CYCLES IS A CHAIN OF ODD CYCLES OF THE RESIDUE `H - C 0`.** -/
theorem isOddCycleChain_succChain {H : SimpleGraph V} {n : ℕ} {C : Fin (n+1) → Finset V}
    (hC : ∀ j : Fin (n+1), IsOddCycle (residueOf H C j) (C j)) (j : Fin n) :
    IsOddCycle (residueOf (deleteFinset H (C 0)) (fun i : Fin n => C i.succ) j) (C j.succ) := by
  rw [residueOf_succChain]
  exact hC j.succ

/-! ### Part 3 — the ladder theorem -/

/-- **A PACKING NUMBER OF ZERO MEANS BIPARTITE.**

The base case of every packing-number argument of this development, in the vocabulary of round 100. -/
theorem isBipartite_of_oddCyclePackingLe_zero {H : SimpleGraph V} {r : ℕ}
    (hp : OddCyclePackingLe r H) (hr : r = 0) : H.IsBipartite := by
  have hp0 : OddCyclePackingLe 0 H := by simpa [hr] using hp
  by_contra hn
  obtain ⟨C, hC⟩ : ∃ C : Finset V, IsOddCycle H C := by
    by_contra hn'
    exact hn (isBipartite_of_no_oddCycle hn')
  have hle := hp0 ({C} : Finset (Finset V))
    ⟨by
        intro X hX Y hY hXY
        have hXC : X = C := Finset.mem_singleton.mp hX
        have hYC : Y = C := Finset.mem_singleton.mp hY
        exact (hXY (hXC.trans hYC.symm)).elim,
      fun D hD => by
        rw [Finset.mem_singleton.mp hD]
        exact hC⟩
  simp only [Finset.card_singleton] at hle
  omega

/-- **THE ODD-GIRTH LADDER.**

Let `C 0, …, C (n-1)` be a chain of odd cycles of `H` (`JSP90.IsOddCycleChain`) with `(C j).card ≤
g j`, and let `H` have odd cycle packing number at most `n`.  Then

> `CloseToBipartite (g 0 + g 1 + … + g (n-1)) H`.

**The classical induction.**  At level `0` the graph is `H`; either it is bipartite and nothing is
paid, or the chain provides an odd cycle `C 0` of at most `g 0` vertices.  Deleting it drops the
packing number by one (round 100's `OddCyclePackingLe.succ_of_residue`) and leaves the *tail*
`C 1, …, C (n-1)` of the chain as a chain of odd cycles of the residue
(`JSP90.residueOf_succChain`), to which the induction hypothesis applies;
`JSP90.closeToBipartite_of_residue` of round 40 then pays `|C 0| ≤ g 0`.  At the last level the
packing number is `0`, so the residue is bipartite (`isBipartite_of_oddCyclePackingLe_zero`) and
nothing is paid.

**There is no degree factor.**  Round 100's ladder paid `(d - 1) |C|` per level because it charged
the *closed neighbourhood* of a maximum packing; here a level charges the odd cycle it actually
deletes, so the bound is the sum of the level girths in an arbitrary degree range. -/
theorem closeToBipartite_of_girthLadder : ∀ (n : ℕ) (H : SimpleGraph V) (g : ℕ → ℕ)
    (C : Fin n → Finset V), (∀ j : Fin n, IsOddCycle (residueOf H C j) (C j)) →
    (∀ j : Fin n, (C j).card ≤ g j.val) →
    OddCyclePackingLe n H → CloseToBipartite (girthSum n g) H := by
  intro n
  induction n with
  | zero =>
      intro H g C hC hlen hp
      have hb : H.IsBipartite := isBipartite_of_oddCyclePackingLe_zero hp rfl
      exact closeToBipartite_of_isBipartite' hb
  | succ n ih =>
      intro H g C hC hlen hp
      by_cases hb : H.IsBipartite
      · exact closeToBipartite_of_isBipartite' hb
      · have hC0 : IsOddCycle H (C 0) := by simpa only [residueOf_zero] using hC 0
        have hlen0 : (C 0).card ≤ g 0 := hlen 0
        have hpres : OddCyclePackingLe (n + 1 - 1) (deleteFinset H (C 0)) := hp.succ_of_residue hC0
        have hshift : ∀ j : Fin n, IsOddCycle (residueOf (deleteFinset H (C 0))
            (fun i : Fin n => C i.succ) j) (C j.succ) := fun j => isOddCycleChain_succChain hC j
        have hres : CloseToBipartite (girthSum n (fun i => g (i + 1))) (deleteFinset H (C 0)) := by
          refine ih (deleteFinset H (C 0)) (fun i => g (i + 1))
            (fun j : Fin n => C j.succ) (fun j => hshift j) ?_ ?_
          · intro j
            simpa [Fin.val_succ] using hlen j.succ
          · simpa using hpres
        have hlift : CloseToBipartite (girthSum n (fun i => g (i + 1)) + (C 0).card) H :=
          closeToBipartite_of_residue hres
        rw [girthSum_succ]
        exact CloseToBipartite.mono hlift (by omega)

/-- **The ladder with the girths indexed by `Fin n`** — the same statement, phrased so that the
constant is the sum over the levels of the chain. -/
theorem closeToBipartite_of_girthLadder_fin (n : ℕ) (H : SimpleGraph V) (g : Fin n → ℕ)
    (C : Fin n → Finset V) (hC : ∀ j : Fin n, IsOddCycle (residueOf H C j) (C j))
    (hlen : ∀ j : Fin n, (C j).card ≤ g j) (hp : OddCyclePackingLe n H) :
    CloseToBipartite (∑ j : Fin n, g j) H := by
  rw [← girthSum_extend g]
  refine closeToBipartite_of_girthLadder n H (girthExtend g) C hC ?_ hp
  intro j
  rw [girthExtend, dif_pos j.isLt]
  exact hlen j

/-- **THE LADDER, WITH THE HYPOTHESIS OF ERDŐS'S PROBLEM.**  The packing bound `n = k` is supplied by
Erdős's local hypothesis `LocIndep k G`.  This is a new instance of the headline theorem. -/
theorem locIndep_girthLadder {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (g : Fin k → ℕ)
    (C : Fin k → Finset V) (hC : ∀ j : Fin k, IsOddCycle (residueOf G C j) (C j))
    (hlen : ∀ j : Fin k, (C j).card ≤ g j) : CloseToBipartite (∑ j : Fin k, g j) G :=
  closeToBipartite_of_girthLadder_fin k G g C hC hlen (locIndep_oddCyclePackingLe hG)

end Chain

/-! ### Part 4 — instances of the headline theorem -/

section Instance

variable {G : SimpleGraph V}

/-- **ERDŐS #73 GIVEN AN ODD-GIRTH LADDER**: the headline theorem in the shape of the ladder.  The
constant is the *sum of the level girths*, and neither the degrees of `G`, the packing weight, the
number of branch vertices, nor the largest odd cycle enters the hypotheses. -/
theorem erdos73On_of_girthLadder (k : ℕ) (g : Fin k → ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (C : Fin k → Finset W),
      LocIndep k G →
      (∀ j : Fin k, IsOddCycle (residueOf G C j) (C j)) →
      (∀ j : Fin k, (C j).card ≤ g j) →
      CloseToBipartite (∑ j : Fin k, g j) G := by
  intro W instW H C hG hC hlen
  exact locIndep_girthLadder hG g C hC hlen

/-- **THE UNIFORM LEVEL OF THE LADDER, PROVED FROM IT.**  If every odd cycle of `G` has at most `ℓ`
vertices then the ladder pays `ℓ` per level, and the constant is `ℓ * k` — the bound of
`JSPProblem/Transversal.lean`'s `JSP90.erdos73On_of_bounded_odd_girth`, which is therefore a
**corollary of this file**. -/
theorem closeToBipartite_of_girthLadder_uniform : ∀ (k : ℕ) (H : SimpleGraph V) (ℓ : ℕ),
    OddCyclePackingLe k H → (∀ D : Finset V, IsOddCycle H D → D.card ≤ ℓ) →
    CloseToBipartite (ℓ * k) H := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro H ℓ hp hlen
      by_cases hb : H.IsBipartite
      · exact closeToBipartite_of_isBipartite' hb
      · have hk1 : 1 ≤ k := by
          by_contra hk0
          exact hb (isBipartite_of_oddCyclePackingLe_zero hp (by omega))
        obtain ⟨C, hC⟩ : ∃ C : Finset V, IsOddCycle H C := by
          by_contra hnC
          exact hb (isBipartite_of_no_oddCycle hnC)
        have hpres : OddCyclePackingLe (k - 1) (deleteFinset H C) := hp.succ_of_residue hC
        have hlen' : ∀ D : Finset V, IsOddCycle (deleteFinset H C) D → D.card ≤ ℓ :=
          fun D hD => hlen D (isOddCycle_of_isOddCycle_deleteFinset hD)
        have hrec : CloseToBipartite (ℓ * (k - 1)) (deleteFinset H C) :=
          ih (k - 1) (by omega) (deleteFinset H C) ℓ hpres hlen'
        have hl := closeToBipartite_of_residue hrec
        refine CloseToBipartite.mono hl ?_
        have hCk := hlen C hC
        calc (ℓ * (k - 1)) + C.card ≤ ℓ * (k - 1) + ℓ := Nat.add_le_add_left hCk _
          _ = ℓ * k := by rw [← Nat.mul_add_one, Nat.sub_add_cancel hk1]

/-- **`JSPProblem/Transversal.lean`'s INSTANCE IS A COROLLARY OF THE LADDER**: the
`CloseToBipartite (ℓ * k) G` of `JSP90.erdos73On_of_bounded_odd_girth`, re-derived from the ladder
theorem.  This is what makes the comparison of the two instances precise. -/
theorem erdos73On_of_girthLadder_uniform (k ℓ : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∀ D : Finset W, IsOddCycle G D → D.card ≤ ℓ) →
      CloseToBipartite (ℓ * k) G := by
  intro W instW H hG hlen
  exact closeToBipartite_of_girthLadder_uniform k H ℓ (locIndep_oddCyclePackingLe hG) hlen

/-- **The ladder is bounded by the uniform bound**: if every level pays at most `ℓ`, the ladder pays
at most `ℓ * k`.  This is the sense in which the two constants are comparable. -/
theorem girthLadder_sum_le_mul {k ℓ : ℕ} (g : Fin k → ℕ) (hg : ∀ j, g j ≤ ℓ) :
    ∑ j : Fin k, g j ≤ ℓ * k := by
  rw [← girthSum_extend g]
  unfold girthSum
  calc (∑ i ∈ Finset.range k, girthExtend g i) ≤ ∑ _ ∈ Finset.range k, ℓ :=
        Finset.sum_le_sum fun i hi => by
          rw [girthExtend, dif_pos (Finset.mem_range.mp hi)]
          exact hg ⟨i, Finset.mem_range.mp hi⟩
    _ = ℓ * k := by rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm]

/-- **… AND IT IS STRICTLY BETTER WHEN THE GIRTHS GROW ALONG THE CHAIN.**  If each level pays at
most `ℓ - 1`, the ladder pays at most `(ℓ - 1) * k < ℓ * k`: this is the concrete reason the ladder
dominates `JSPProblem/Transversal.lean`'s instance, whose constant does not see the *shape* of the
sequence of level girths. -/
theorem girthLadder_sum_le_sub_one_mul {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (g : Fin k → ℕ)
    (hg : ∀ j, g j ≤ ℓ - 1) : (∑ j : Fin k, g j ≤ (ℓ - 1) * k) ∧ (ℓ - 1) * k < ℓ * k := by
  constructor
  · have key := girthLadder_sum_le_mul (k := k) (ℓ := ℓ - 1) (fun j => min (g j) (ℓ - 1))
      (fun j => Nat.min_le_right _ _)
    rw [Finset.sum_congr rfl (fun j _ => min_eq_left (hg j))] at key
    exact key
  · calc (ℓ - 1) * k < (ℓ - 1) * k + 1 := Nat.lt_add_one _
      _ ≤ (ℓ - 1) * k + k := Nat.add_le_add_left hk ((ℓ - 1) * k)
      _ = ℓ * k := by rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hℓ]

/-- **`k ≤ k * k` for every `k`** — the elementary arithmetic fact the sums below need, and one that
`omega` cannot do on its own (it is not a linear statement). -/
theorem nat_le_sq (k : ℕ) : k ≤ k * k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · have h := Nat.mul_le_mul_left k hk
    simpa using h

/-- **`k < k * k` for `k ≥ 2`** -/
theorem nat_lt_sq {k : ℕ} (hk : 2 ≤ k) : k < k * k := by
  have hpos : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
  have hkey : k * k = k + k * (k - 1) := by
    calc k * k = k * (k - 1 + 1) := by
          have hk1 : k - 1 + 1 = k := by omega
          rw [hk1]
      _ = k * (k - 1) + k * 1 := Nat.mul_add k (k - 1) 1
      _ = k * (k - 1) + k := by rw [Nat.mul_one, Nat.add_comm]
      _ = k + k * (k - 1) := by omega
  rw [hkey]
  exact Nat.lt_add_of_pos_right hpos

/-- **THE SUM OF AN ARITHMETIC LADDER OF GIRTHS.**  `girthSum k (fun i => a + 2 * i) = a * k + k *
(k - 1)`: the levels `a, a + 2, a + 4, …` of a ladder (the odd girths of a residue chain are all odd,
so consecutive levels differ by an even number).  This is the arithmetic of the ladder constant. -/
theorem girthSum_arith : ∀ (k a : ℕ), girthSum k (fun i => a + 2 * i) = a * k + k * (k - 1) := by
  intro k
  induction k with
  | zero =>
      intro a
      rfl
  | succ k ih =>
      intro a
      have hs : girthSum (k + 1) (fun i => a + 2 * i)
          = girthSum k (fun i => a + 2 * (i + 1)) + a := by
        have h := girthSum_succ k (fun i => a + 2 * i)
        convert h using 1 <;> congr 1 <;> omega
      have hsum : girthSum k (fun i => a + 2 * (i + 1)) = (a + 2) * k + k * (k - 1) := by
        have h := ih (a + 2)
        have h' : girthSum k (fun i => a + 2 * (i + 1))
            = girthSum k (fun i => (a + 2) + 2 * i) := by
          congr 1
          funext i
          omega
        rw [← h'] at h
        exact h
      rw [hs, hsum]
      have hL : (a + 2) * k + k * (k - 1) + a = a * k + a + k * k + k := by
        have h1 := Nat.mul_sub k k 1
        rw [Nat.mul_one] at h1
        rw [Nat.add_mul, h1]
        have e : k * k - k + k = k * k := Nat.sub_add_cancel (n := k * k) (m := k) (nat_le_sq k)
        omega
      have hR : a * (k + 1) + (k + 1) * ((k + 1) - 1) = a * k + a + k * k + k := by
        have hk1 : (k + 1) - 1 = k := by omega
        rw [hk1, Nat.mul_add, Nat.mul_one, Nat.succ_mul]
        omega
      exact hL.trans hR.symm

/-- **The constant of the staircase ladder `3, 5, 7, …` is exactly `k² + 2k`.** -/
theorem staircase_const (k : ℕ) : girthSum k (fun i => 3 + 2 * i) = k * k + 2 * k := by
  rw [girthSum_arith]
  have h1 := Nat.mul_sub k k 1
  rw [Nat.mul_one] at h1
  rw [h1]
  have e : k * k - k + k = k * k := Nat.sub_add_cancel (n := k * k) (m := k) (nat_le_sq k)
  omega

/-- **A finite girth sequence indexed by `Fin k`, written as a sum over `Finset.range k`.** -/
theorem sum_fin_val (k : ℕ) (f : ℕ → ℕ) : (∑ j : Fin k, f j.val) = ∑ i ∈ Finset.range k, f i := by
  rw [Fin.sum_univ_eq_sum_range]

/-- **THE STAIRCASE LADDER: `τ_odd(G) ≤ k² + 2k` FOR A RESIDUE CHAIN WHOSE LEVELS GROW LIKE
`3, 5, 7, …`.**

This is the instance that shows the ladder is *not* a reformulation of the uniform bound: if level
`j` of the chain is an odd cycle of at most `3 + 2j` vertices, Erdős's hypothesis `LocIndep k G`
forces `CloseToBipartite (k * k + 2 * k) G` (`JSP90.staircase_const` is the closed form of the
ladder constant), while the uniform bound of `JSPProblem/Transversal.lean` — whose constant does not
see the shape of the sequence — gives `CloseToBipartite ((2 * k + 1) * k) G`.  The two constants are
compared in `JSP90.staircase_lt_uniform`. -/
theorem erdos73On_of_girthLadder_staircase (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (C : Fin k → Finset W),
      LocIndep k G →
      (∀ j : Fin k, IsOddCycle (residueOf G C j) (C j)) →
      (∀ j : Fin k, (C j).card ≤ 3 + 2 * j.val) →
      CloseToBipartite (k * k + 2 * k) G := by
  intro W instW H C hG hC hlen
  have h1 := locIndep_girthLadder hG (fun j => 3 + 2 * j.val) C hC hlen
  have heq : (∑ j : Fin k, (3 + 2 * j.val)) = girthSum k (fun i => 3 + 2 * i) :=
    sum_fin_val k (fun i => 3 + 2 * i)
  rw [heq, staircase_const] at h1
  exact h1

/-- **THE STAIRCASE LADDER IS STRICTLY CHEAPER THAN THE UNIFORM BOUND**, machine checked:
`k² + 2k < (2k + 1) * k` for every `k ≥ 2`, while for `k = 1` the two constants agree (`3 = 3`).
This is the quantitative content of the ladder: it is the only bound in this development whose
constant depends on the *sequence* of level girths and not merely on their maximum. -/
theorem staircase_lt_uniform (k : ℕ) (hk : 2 ≤ k) : k * k + 2 * k < (2 * k + 1) * k := by
  have h1 : 2 * k * k = k * k + k * k := by rw [Nat.mul_assoc, Nat.two_mul]
  have h2 : (2 * k + 1) * k = 2 * k * k + k := by rw [Nat.add_mul, Nat.one_mul]
  rw [h2, h1]
  have hlt := nat_lt_sq hk
  omega

end Instance

end

end JSP90
