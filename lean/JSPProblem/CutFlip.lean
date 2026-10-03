/-
# JSP-000090 — round 128: the **FLIP EQUIVALENCE** of a maximum cut, and the REFUTATION of the
# max-cut route

`discovery/JSP-000090/policy.json` (round 127) opened the maximum-cut axis and left one *named*
blocker behind:

> THE ONE-VERTEX-FLIP EQUIVALENCE IS NOT FORMALISED: `JSP90.StableCut` is stated directly (it is
> the flip condition by definition) rather than as "A is a maximum cut".  The missing lemma is that
> `MaxCut G A -> SameDeg G A v <= CrossDeg G A v` for `v in A`.

Part 1 proves exactly that, together with the arithmetic it rests on (**the per-vertex delta** of
the size of a cut, `JSP90.cutSize_flip`) and with the **existence of a maximum cut** for every
finite graph — the first cut in the development that is produced *from* `G` and is *optimal* for it.

Part 2 turns optimality into a count: at a maximum cut the monochromatic vertices are few
(`JSP90.card_monoSet_le_two_mul_cutSize_of_isMaxCut`) and the cut carries at least half of the edges
(`JSP90.edgeCount_le_two_mul_cutSize_of_isMaxCut`, the classical max-cut bound).

Part 3 restates the round-127 reduction with *maximum* cuts rather than *stable* ones; the two are
equivalent in strength (`JSP90.maxCutMonoLe_of_maxCutOfMonoCardLe`).

Part 4 is the **negative result**, and it is why this axis must not be tried again:
`JSP90.not_maxCutMonoLe` refutes `JSP90.MaxCutMonoLe` for *every* constant `c`, and
`JSP90.not_maxCutOfMonoCardLe` does the same for the maximum-cut version.  No bound on the mono set
of a stable or maximum cut — however weak — can prove Erdős #73.

Why it fails: the mono set of a cut must contain a transversal of the odd cycles, and the cuts that
save vertices on the triangles of `G` save them on triangles that `K_{c + 2}` does not have.  The
witness is the complete graph `K_{c + 2}`: it satisfies `LocIndep c`, and its optimal odd cycle
transversal number is `c` (`JSP90.closeToBipartite_iff_completeGraph_add_two`), while *every* cut
certifies at least `c + 1` vertices (round 127's
`JSP90.card_monoSet_ge_card_sub_one_completeGraph`).  The certificate misses the optimum by exactly
one vertex, and `K_n` is not even the worst case: the windmill family of `JSPProblem/MonoWind.lean`
has the optimal transversal number `1` and `MaxDef = 1` while *every* cut certifies `t + 1`
vertices, which refutes even the *relative* form `card (MonoSet G A) ≤ phi (MaxDef G)` that round
127 recorded as the surviving hypothesis.

Nothing here is assumed: `JSP90.MaxCutMonoLe` and `JSP90.MaxCutOfMonoCardLe` are `def`s that are
never inhabited, and `JSP90.not_maxCutMonoLe` says so.  `JSP90.OddCycleErdosPosa r` and hence
`jsp_000090_main` are unchanged.
-/

import JSPProblem.Mono
import JSPProblem.Sparse

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqCutFlip : DecidableEq V := Classical.decEq V


/-! ### Part 0 — counting helpers -/

/-- **REMOVING ONE ELEMENT FROM A FINSET CHANGES THE CARDINALITY OF A FILTER BY AT MOST ONE**, and
the difference is recorded exactly. -/
lemma card_filter_erase_sub (s : Finset V) (p : V → Prop) [DecidablePred p] (a : V) :
    (s.filter p).card = ((s.erase a).filter p).card + (if a ∈ s ∧ p a then 1 else 0) := by
  rw [Finset.filter_erase]
  by_cases h : a ∈ s.filter p
  · have h' : a ∈ s ∧ p a := Finset.mem_filter.mp h
    rw [if_pos h', Finset.card_erase_add_one h]
  · have hne : ¬ (a ∈ s ∧ p a) := fun hp => h (Finset.mem_filter.mpr hp)
    rw [if_neg hne, Finset.erase_eq_of_notMem h, Nat.add_zero]

/-- **`∑ x ∈ s, (if p x then 1 else 0)` COUNTS THE FILTER.** -/
lemma sum_if_card_filter (s : Finset V) (p : V → Prop) [DecidablePred p] :
    (∑ x ∈ s, if p x then (1 : ℕ) else 0) = (s.filter p).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp

/-- **SUMMING OVER THE WHOLE VERTEX SET SPLITS OVER A FINDSET AND ITS COMPLEMENT.** -/
lemma sum_univ_eq_sum_split (s : V → ℕ) (t : Finset V) :
    (∑ v : V, s v) = ∑ v ∈ t, s v + ∑ v ∈ Finset.univ \ t, s v := by
  have hd : Disjoint t (Finset.univ \ t) :=
    fun a ha1 ha2 => (Finset.sdiff_disjoint (s := t) (t := Finset.univ) ha2 ha1)
  have hdecomp : t ∪ Finset.univ \ t = (Finset.univ : Finset V) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have h := Finset.sum_union (s₁ := t) (s₂ := Finset.univ \ t) (f := fun v => s v) hd
  rw [hdecomp] at h
  exact h

/-- **THE TYPE-INDEXED SUM AND THE FINSET SUM OVER `univ` AGREE.** -/
lemma sum_type_eq_sum_univ (s : V → ℕ) :
    (∑ v : V, s v) = ∑ v ∈ (Finset.univ : Finset V), s v := rfl

lemma filter_eq_singleton (s : Finset V) (v : V) :
    s.filter (fun w => w = v) = if v ∈ s then ({v} : Finset V) else ∅ := by
  by_cases hs : v ∈ s
  · rw [if_pos hs]
    ext y
    constructor
    · intro hy
      rw [(Finset.mem_filter.mp hy).2]
      exact Finset.mem_singleton.mpr rfl
    · intro hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact Finset.mem_filter.mpr ⟨hs, rfl⟩
  · rw [if_neg hs]
    ext y
    constructor
    · intro hy
      have h2 := Finset.mem_filter.mp hy
      have hyn : ¬ (y ∈ s) := by rw [h2.2]; exact hs
      exact absurd h2.1 hyn
    · intro hy
      simp at hy

lemma card_filter_notMem_erase {A s : Finset V} {v : V} (hvA : v ∈ A) :
    (s.filter (fun w => w ∉ A.erase v)).card
      = (s.filter (fun w => w ∉ A)).card + (if v ∈ s then 1 else 0) := by
  have hfilter : s.filter (fun w => w ∉ A.erase v) = s.filter (fun w => w = v ∨ w ∉ A) := by
    ext y
    constructor
    · intro hy
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, ?_⟩
      by_cases hyv : y = v
      · exact Or.inl hyv
      · exact Or.inr fun hyA => (Finset.mem_filter.mp hy).2 (Finset.mem_erase.mpr ⟨hyv, hyA⟩)
    · intro hy
      have h2 := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨h2.1, ?_⟩
      rcases h2.2 with rfl | hy
      · intro hyin
        exact (Finset.mem_erase.mp hyin).1 rfl
      · intro hyin
        exact hy (Finset.mem_erase.mp hyin).2
  have hdisj : Disjoint (s.filter (fun w => w = v)) (s.filter (fun w => w ∉ A)) :=
    Finset.disjoint_left.2 fun y hy1 hy2 =>
      (Finset.mem_filter.mp hy2).2 (by rw [(Finset.mem_filter.mp hy1).2]; exact hvA)
  have hcard_eq : (s.filter (fun w => w = v)).card = (if v ∈ s then 1 else 0) := by
    by_cases hs : v ∈ s
    · rw [filter_eq_singleton, if_pos hs, Finset.card_singleton, if_pos hs]
    · rw [filter_eq_singleton, if_neg hs, Finset.card_empty, if_neg hs]
  have hunion : (s.filter (fun w => w = v)) ∪ (s.filter (fun w => w ∉ A))
      = s.filter (fun w => w = v ∨ w ∉ A) :=
    (Finset.filter_or (fun w => w = v) (fun w => w ∉ A) s).symm
  rw [hfilter, ← hunion, Finset.card_union_of_disjoint hdisj, hcard_eq]
  exact Nat.add_comm _ _

/-- **ERASING `v` FROM `A` DOES NOT CHANGE THE NUMBER OF NEIGHBOURS OF `v` INSIDE `A`** — the
neighbourhood of `v` never contains `v` itself. -/
lemma card_filter_neigh_mem_erase {A : Finset V} {v : V} (hvA : v ∈ A) :
    ((A.erase v).filter (fun x => v ∈ Neigh G x)).card
      = ((Neigh G v).filter (fun w => w ∈ A)).card := by
  classical
  have hmem (y : V) :
      (y ∈ (A.erase v).filter (fun x => v ∈ Neigh G x))
        ↔ (y ∈ (Neigh G v).filter (fun w => w ∈ A)) := by
    constructor
    · intro hy
      have h1 := Finset.mem_erase.mp (Finset.mem_filter.mp hy).1
      have h2 : G.Adj y v := by
        simpa [Neigh] using (Finset.mem_filter.mp (Finset.mem_filter.mp hy).2)
      exact Finset.mem_filter.mpr ⟨by simpa [Neigh] using h2.symm, h1.2⟩
    · intro hy
      have h1 := Finset.mem_filter.mp hy
      have hadj : G.Adj v y := by simpa [Neigh] using h1.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨fun hyv => G.irrefl (hyv ▸ hadj), h1.2⟩,
          by simpa [Neigh] using hadj.symm⟩
  exact congrArg Finset.card (Finset.ext fun y => hmem y)

/-! ### Part 1 — the size of a cut, the flip delta, and the flip equivalence -/

/-- **`CutSize G A` is the number of edges crossing the cut with side `A`**, each counted once, from
its endpoint in `A`.  This is the quantity a maximum cut maximises. -/
noncomputable def CutSize (G : SimpleGraph V) (A : Finset V) : ℕ :=
  ∑ v ∈ A, CrossDeg G A v

/-- **FLIPPING `v` FROM `A` TO THE OTHER SIDE CHANGES THE SIZE OF THE CUT BY
`+ SameDeg − CrossDeg`**: the edges from `v` to its own side start crossing, and those to the other
side stop crossing.  This is the arithmetic the flip equivalence rests on. -/
theorem cutSize_flip {A : Finset V} {v : V} (hvA : v ∈ A) :
    CutSize G (A.erase v) + CrossDeg G A v = CutSize G A + SameDeg G A v := by
  have hstep : ∀ x ∈ A.erase v,
      CrossDeg G (A.erase v) x
        = CrossDeg G A x + (if v ∈ Neigh G x then (1 : ℕ) else 0) := by
    intro x _
    have hcard := card_filter_notMem_erase (A := A) (s := Neigh G x) hvA
    unfold CrossDeg
    omega
  have hsumA : CutSize G A
      = (∑ x ∈ A.erase v, CrossDeg G A x) + CrossDeg G A v := by
    have hins : insert v (A.erase v) = A := Finset.insert_erase hvA
    have h := Finset.sum_insert (s := A.erase v) (a := v) (f := fun x => CrossDeg G A x)
      (fun h => (Finset.mem_erase.mp h).1 rfl)
    rw [hins] at h
    have h1 : CutSize G A = CrossDeg G A v + (∑ x ∈ A.erase v, CrossDeg G A x) := h
    rw [h1, Nat.add_comm]
  have hsumNe : (∑ x ∈ A.erase v, if v ∈ Neigh G x then (1 : ℕ) else 0)
      = ((A.erase v).filter (fun x => v ∈ Neigh G x)).card := sum_if_card_filter _ _
  have hsumNe' : ((A.erase v).filter (fun x => v ∈ Neigh G x)).card = SameDeg G A v :=
    card_filter_neigh_mem_erase hvA
  have hflip : CutSize G (A.erase v)
      = (∑ x ∈ A.erase v, CrossDeg G A x) + SameDeg G A v := by
    unfold CutSize
    rw [Finset.sum_congr rfl fun x hx => hstep x hx, Finset.sum_add_distrib, hsumNe, hsumNe']
  rw [hflip, hsumA]
  omega

/-- **COMPLEMENTING THE CUT SWAPS THE TWO KINDS OF DEGREE AT EVERY VERTEX** (this is the
pointwise form; `JSP90.cutSize_compl` below is the global one). -/
lemma crossDeg_compl_eq_sameDeg (A : Finset V) (v : V) :
    CrossDeg G (Finset.univ \ A) v = SameDeg G A v := by
  classical
  have heqfilt : (Neigh G v).filter (fun w => w ∉ Finset.univ \ A)
      = (Neigh G v).filter (fun w => w ∈ A) := by
    apply Finset.ext
    intro w
    constructor
    · intro h
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, ?_⟩
      have h1 : w ∈ (Finset.univ : Finset V).filter (fun u => G.Adj v u) :=
        (Finset.mem_filter.mp h).1
      by_contra hA
      exact (Finset.mem_filter.mp h).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp h1).1, hA⟩)
    · intro h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, by
        intro hw
        exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_filter.mp h).2⟩
  unfold CrossDeg SameDeg
  rw [heqfilt]

/-- ... and the other way round. -/
lemma sameDeg_compl_eq_crossDeg (A : Finset V) (v : V) :
    SameDeg G (Finset.univ \ A) v = CrossDeg G A v := by
  classical
  have heqfilt : (Neigh G v).filter (fun w => w ∈ Finset.univ \ A)
      = (Neigh G v).filter (fun w => w ∉ A) := by
    apply Finset.ext
    intro w
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, fun hA =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).2).2 hA⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, (Finset.mem_filter.mp h).2⟩⟩
  unfold SameDeg CrossDeg
  rw [heqfilt]

/-- **THE SIZE OF A CUT DOES NOT DEPEND ON WHICH SIDE IS CALLED `A`** — the crossing edges are
counted once from each side, so `CutSize G (V \ A) = CutSize G A`. -/
theorem cutSize_compl (A : Finset V) : CutSize G (Finset.univ \ A) = CutSize G A := by
  classical
  have hsum (v : V) : SameDeg G A v
      = ∑ w ∈ A, (if G.Adj v w then (1 : ℕ) else 0) := by
    have heq : A.filter (fun w => G.Adj v w) = (Neigh G v).filter (fun w => w ∈ A) := by
      apply Finset.ext
      intro w
      simp [mem_neigh, and_comm]
    rw [SameDeg, ← heq, sum_if_card_filter]
  calc CutSize G (Finset.univ \ A)
      = ∑ v ∈ Finset.univ \ A, SameDeg G A v := by
          unfold CutSize
          exact Finset.sum_congr rfl fun v _ => crossDeg_compl_eq_sameDeg A v
      _ = ∑ v ∈ Finset.univ \ A, ∑ w ∈ A, (if G.Adj v w then (1 : ℕ) else 0) := by
          exact Finset.sum_congr rfl fun v _ => hsum v
      _ = ∑ w ∈ A, ∑ v ∈ Finset.univ \ A, (if G.Adj w v then (1 : ℕ) else 0) := by
          calc (∑ v ∈ Finset.univ \ A, ∑ w ∈ A, (if G.Adj v w then (1 : ℕ) else 0))
              = ∑ w ∈ A, ∑ v ∈ Finset.univ \ A, (if G.Adj v w then (1 : ℕ) else 0) :=
              Finset.sum_comm (s := Finset.univ \ A) (t := A)
                (f := fun v w => if G.Adj v w then (1 : ℕ) else 0)
            _ = ∑ w ∈ A, ∑ v ∈ Finset.univ \ A, (if G.Adj w v then (1 : ℕ) else 0) := by
              refine Finset.sum_congr rfl fun w _ => ?_
              refine Finset.sum_congr rfl fun v _ => ?_
              by_cases h : G.Adj v w
              · rw [if_pos h, if_pos h.symm]
              · rw [if_neg h, if_neg (fun h2 => h h2.symm)]
      _ = ∑ w ∈ A, CrossDeg G A w := by
          refine Finset.sum_congr rfl fun w _ => ?_
          have heq : (Finset.univ \ A).filter (fun v => G.Adj w v)
              = (Neigh G w).filter (fun v => v ∉ A) := by
            apply Finset.ext
            intro v
            simp [mem_neigh, and_comm]
          rw [CrossDeg, ← heq, sum_if_card_filter]
      _ = CutSize G A := rfl

/-- **`A` is a MAXIMUM CUT when no other cut is bigger.** -/
def IsMaxCut (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ B : Finset V, CutSize G B ≤ CutSize G A

/-- **THE FLIP EQUIVALENCE: EVERY MAXIMUM CUT IS STABLE.**

This is the link `discovery/JSP-000090/policy.json` (round 127) named as the missing lemma between
the word "stable" and the word "maximum": if some vertex of `A` had more neighbours on its own side
than on the other, flipping it would *increase* the size of the cut, contradicting maximality. -/
theorem stableCut_of_isMaxCut {A : Finset V} (hA : IsMaxCut G A) : StableCut G A := by
  intro v hvA
  have hle : CutSize G (A.erase v) ≤ CutSize G A := hA (A.erase v)
  have hflip := cutSize_flip (G := G) (A := A) hvA
  omega

/-- **EVERY FINITE GRAPH HAS A MAXIMUM CUT.**  (The first cut in this development that is produced
from `G` itself and is *optimal* for it.) -/
theorem exists_maxCut : ∃ A : Finset V, IsMaxCut G A := by
  classical
  set S : Finset ℕ := (Finset.univ : Finset V).powerset.image (CutSize G) with hS
  have hne : S.Nonempty := (Finset.powerset_nonempty (Finset.univ : Finset V)).image (CutSize G)
  set c : ℕ := S.max' hne with hc
  have hcmem : c ∈ S := Finset.max'_mem _ _
  obtain ⟨A, hA, hAc⟩ := Finset.mem_image.mp hcmem
  refine ⟨A, fun B => ?_⟩
  have hB : CutSize G B ∈ S := by
    rw [hS]
    exact Finset.mem_image.mpr
      ⟨B, Finset.mem_powerset.mpr (Finset.subset_univ B), rfl⟩
  calc CutSize G B ≤ S.max' ⟨CutSize G B, hB⟩ := Finset.le_max' S _ hB
    _ = c := hc.symm
    _ = CutSize G A := hAc.symm

/-- **EVERY FINITE GRAPH HAS A MAXIMUM CUT, AND IT IS STABLE.** -/
theorem exists_maxCut_stable : ∃ A : Finset V, IsMaxCut G A ∧ StableCut G A := by
  obtain ⟨A, hA⟩ := exists_maxCut (G := G)
  exact ⟨A, hA, stableCut_of_isMaxCut hA⟩

/-- **THE CONCLUSION OF ERDŐS #73 FOR THE MONO SET OF A MAXIMUM CUT.**  For every finite graph there
is an *optimal* cut whose mono set is an odd cycle transversal. -/
theorem exists_maxCut_closeToBipartite :
    ∃ A : Finset V, IsMaxCut G A ∧ CloseToBipartite (MonoSet G A).card G := by
  obtain ⟨A, hA⟩ := exists_maxCut (G := G)
  exact ⟨A, hA, closeToBipartite_monoSet (G := G) (A := A)⟩

/-! ### Part 2 — what optimality of a cut buys: few mono vertices, half the edges -/

/-- **AT A MAXIMUM CUT THE INTERNAL DEGREES OF A SIDE NUMBER AT MOST THE SIZE OF THE CUT.** -/
theorem sum_sameDeg_le_cutSize_of_isMaxCut {A : Finset V} (hA : IsMaxCut G A) :
    (∑ v ∈ A, SameDeg G A v) ≤ CutSize G A :=
  Finset.sum_le_sum fun v hvA => stableCut_of_isMaxCut hA v hvA

/-- **`SameDeg G A v` is positive whenever `v ∈ A` is a mono vertex of `A`**: a mono vertex of a side
has a neighbour on that very side. -/
lemma sameDeg_pos_of_mem_monoSet {A : Finset V} {v : V} (hvA : v ∈ A)
    (hvM : v ∈ MonoSet G A) : 0 < SameDeg G A v := by
  obtain ⟨w, hwA, hadj⟩ := (monoVertex_of_mem (G := G) hvA).mp (mem_monoSet.mp hvM)
  rw [SameDeg]
  exact Finset.card_pos.mpr
    ⟨w, Finset.mem_filter.mpr ⟨mem_neigh.mpr hadj, hwA⟩⟩

/-- **THE MONO VERTICES OF A SIDE ARE COUNTED BY THE INTERNAL DEGREES OF THAT SIDE.** -/
lemma card_monoSide_le_sum_sameDeg {A : Finset V} :
    (A ∩ MonoSet G A).card ≤ ∑ v ∈ A, SameDeg G A v := by
  set T : Finset V := A.filter (fun v => 0 < SameDeg G A v) with hT
  have hsub : A ∩ MonoSet G A ⊆ T := by
    intro v hv
    have hv' : v ∈ A ∧ v ∈ MonoSet G A := Finset.mem_inter.mp hv
    exact Finset.mem_filter.mpr ⟨hv'.1, sameDeg_pos_of_mem_monoSet hv'.1 hv'.2⟩
  have h1 : T.card ≤ ∑ v ∈ A, SameDeg G A v := by
    have hstep : ∀ v ∈ T, (1 : ℕ) ≤ SameDeg G A v := fun v hv => by
      rw [hT, Finset.mem_filter] at hv
      omega
    have h2 : T.card = ∑ v ∈ T, (1 : ℕ) := Finset.card_eq_sum_ones T
    have h3 : (∑ v ∈ T, (1 : ℕ)) ≤ ∑ v ∈ T, SameDeg G A v :=
      Finset.sum_le_sum fun v hv => hstep v hv
    calc T.card = ∑ v ∈ T, (1 : ℕ) := h2
      _ ≤ ∑ v ∈ T, SameDeg G A v := h3
      _ ≤ ∑ v ∈ A, SameDeg G A v :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset (fun v => 0 < SameDeg G A v) A)
  have h2 := Finset.card_le_card hsub
  omega

/-- **AT A MAXIMUM CUT, EACH SIDE HAS AT MOST `CutSize` MONOCHROMATIC VERTICES.** -/
theorem card_monoSide_le_cutSize_of_isMaxCut {A : Finset V} (hA : IsMaxCut G A) :
    (A ∩ MonoSet G A).card ≤ CutSize G A :=
  le_trans (card_monoSide_le_sum_sameDeg (G := G) (A := A))
    (sum_sameDeg_le_cutSize_of_isMaxCut hA)

/-- **THE MONO SET SPLITS OVER THE TWO SIDES OF THE CUT**, and the two parts are exchanged by
`monoSet_compl`. -/
theorem monoSet_eq_inter_union_inter {A : Finset V} :
    MonoSet G A = (A ∩ MonoSet G A) ∪ ((Finset.univ \ A) ∩ MonoSet G (Finset.univ \ A)) := by
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_monoSet_compl]
  tauto

/-- **THE MONO SET OF A MAXIMUM CUT HAS AT MOST TWICE THE SIZE OF THE CUT:**
`card (MonoSet G A) ≤ 2 * CutSize G A`, for every maximum cut `A`. -/
theorem card_monoSet_le_two_mul_cutSize_of_isMaxCut {A : Finset V} (hA : IsMaxCut G A) :
    (MonoSet G A).card ≤ 2 * CutSize G A := by
  have hcompl : IsMaxCut G (Finset.univ \ A) := by
    intro C
    rw [cutSize_compl]
    exact hA C
  have hA' := card_monoSide_le_cutSize_of_isMaxCut hA
  have hB' := card_monoSide_le_cutSize_of_isMaxCut hcompl
  have hcut : CutSize G (Finset.univ \ A) = CutSize G A := cutSize_compl A
  have hle : ((Finset.univ \ A) ∩ MonoSet G (Finset.univ \ A)).card
      = ((Finset.univ \ A) ∩ MonoSet G A).card := by rw [monoSet_compl]
  have hcard : (MonoSet G A).card
      ≤ (A ∩ MonoSet G A).card + ((Finset.univ \ A) ∩ MonoSet G (Finset.univ \ A)).card := by
    calc (MonoSet G A).card
        = ((A ∩ MonoSet G A) ∪ ((Finset.univ \ A) ∩ MonoSet G (Finset.univ \ A))).card :=
          congrArg Finset.card (monoSet_eq_inter_union_inter (G := G) (A := A))
        _ ≤ (A ∩ MonoSet G A).card
            + ((Finset.univ \ A) ∩ MonoSet G (Finset.univ \ A)).card :=
          Finset.card_union_le _ _
  rw [hle] at hcard
  omega

/-- **A MAXIMUM CUT CARRIES AT LEAST HALF OF THE EDGES** — the classical maximum-cut bound, in the
language of this development: `edgeCount G ≤ 2 * CutSize G A` for every maximum cut `A`. -/
theorem edgeCount_le_two_mul_cutSize_of_isMaxCut {A : Finset V} (hA : IsMaxCut G A) :
    edgeCount G ≤ 2 * CutSize G A := by
  have hcut : CutSize G (Finset.univ \ A) ≤ CutSize G A := hA (Finset.univ \ A)
  have h1 : 2 * edgeCount G
      = ∑ v ∈ (Finset.univ : Finset V), SameDeg G A v
        + ∑ v ∈ (Finset.univ : Finset V), CrossDeg G A v := by
    have h2 := two_mul_edgeCount (G := G)
    have h5 : degSum G = ∑ v ∈ (Finset.univ : Finset V), (Neigh G v).card := by
      unfold degSum
      exact sum_type_eq_sum_univ _
    have h4 : ∑ v ∈ (Finset.univ : Finset V), (Neigh G v).card
        = ∑ v ∈ (Finset.univ : Finset V), SameDeg G A v
          + ∑ v ∈ (Finset.univ : Finset V), CrossDeg G A v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => (sameDeg_add_crossDeg (G := G) A v).symm
    rw [h2, h5, h4]
  have h2 : (∑ v ∈ (Finset.univ : Finset V), SameDeg G A v) ≤ 2 * CutSize G A := by
    rw [sum_univ_eq_sum_split (SameDeg G A) A]
    have hA' := sum_sameDeg_le_cutSize_of_isMaxCut hA
    have hB' : (∑ v ∈ Finset.univ \ A, CrossDeg G (Finset.univ \ A) v) ≤ CutSize G A := by
      have h1 : (∑ v ∈ Finset.univ \ A, CrossDeg G (Finset.univ \ A) v)
          = CutSize G (Finset.univ \ A) := rfl
      rw [h1, cutSize_compl]
    have hmid : (∑ v ∈ Finset.univ \ A, SameDeg G A v)
        ≤ ∑ v ∈ Finset.univ \ A, CrossDeg G (Finset.univ \ A) v :=
      Finset.sum_le_sum fun v _ => by rw [(crossDeg_compl_eq_sameDeg (G := G) A v).symm]
    omega
  have h3 : (∑ v ∈ (Finset.univ : Finset V), CrossDeg G A v) ≤ 2 * CutSize G A := by
    rw [sum_univ_eq_sum_split (CrossDeg G A) A]
    have hcompl : IsMaxCut G (Finset.univ \ A) := by
      intro C
      rw [cutSize_compl]
      exact hA C
    have hB' := sum_sameDeg_le_cutSize_of_isMaxCut hcompl
    have hcut : CutSize G (Finset.univ \ A) ≤ CutSize G A := hA (Finset.univ \ A)
    have hsumA : (∑ v ∈ A, CrossDeg G A v) = CutSize G A := rfl
    refine le_trans
      (add_le_add (Nat.le_refl (∑ v ∈ A, CrossDeg G A v))
        (Finset.sum_le_sum (fun v hv =>
          by rw [(sameDeg_compl_eq_crossDeg (G := G) A v).symm]))) ?_
    omega
  omega

/-! ### Part 3 — the reduction with *maximum* cuts -/

universe u

/-- **THE CLASS-LEVEL HYPOTHESIS OF THE MAXIMUM-CUT ROUTE, RESTATED WITH MAXIMUM CUTS**:
every finite graph of deficiency `≤ k` has a **maximum** cut whose mono set has at most `c`
vertices.  A `def`, and — by `JSP90.not_maxCutOfMonoCardLe` — false for every `c`. -/
def MaxCutOfMonoCardLe (c : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (k : ℕ), LocIndep k G →
    ∃ A : Finset W, IsMaxCut G A ∧ (MonoSet G A).card ≤ c

/-- **A MAXIMUM CUT WITH A SMALL MONO SET GIVES THE CONCLUSION OF ERDŐS #73**, with constant `c`
independent of `k`. -/
theorem erdos73On_of_maxCutOfMonoCardLe (c : ℕ) (h : MaxCutOfMonoCardLe.{u} c) :
    Erdős73On.{u} c c := by
  intro W instW G hG
  obtain ⟨A, _, hcard⟩ := h W instW G c hG
  have h1 := closeToBipartite_monoSet (G := G) (A := A)
  refine h1.mono (m' := c) ?_
  omega

/-- **... and hence the whole of JSP-000090.** -/
theorem erdos73_of_maxCutOfMonoCardLe (c : ℕ) (h : MaxCutOfMonoCardLe.{u} c) : Erdős73.{u} c :=
  ⟨c, erdos73On_of_maxCutOfMonoCardLe c h⟩

/-- **THE MAXIMUM-CUT HYPOTHESIS IMPLIES THE STABLE-CUT HYPOTHESIS** (`stableCut_of_isMaxCut`):
a maximum cut is stable, so a bound on the mono set of a maximum cut bounds the mono set of some
stable cut.  The two reductions are equivalent in strength. -/
theorem maxCutMonoLe_of_maxCutOfMonoCardLe (c : ℕ) (h : MaxCutOfMonoCardLe.{u} c) :
    MaxCutMonoLe.{u} c := by
  intro W instW G k hk
  obtain ⟨A, hA, hcard⟩ := h W instW G k hk
  exact ⟨A, stableCut_of_isMaxCut hA, hcard⟩

/-! ### Part 4 — the NEGATIVE result: the max-cut route is refuted for every constant -/

/-- **`K_n` HAS NO CUT WHOSE MONO SET HAS FEWER THAN `n − 1` VERTICES** — precisely, if
`c + 2 ≤ n` then no cut of `K_n` has a mono set of at most `c` vertices, so the complete graph is
the witness against the max-cut route.  For `n ≥ 4` this is round 127's
`card_monoSet_ge_card_sub_one_completeGraph` (its bound `n − 1` is attained, e.g. by a singleton
side, `card_monoSet_singleton_completeGraph`); `n = 3` follows from `K_3` being non-bipartite. -/
theorem not_exists_monoCard_le_completeGraph {n : ℕ} {c : ℕ} (hn : 3 ≤ n) (hc : c + 2 ≤ n) :
    ¬ ∃ A : Finset (Fin n), (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card ≤ c := by
  by_cases hn4 : 4 ≤ n
  · rintro ⟨A, hA⟩
    have h1 := card_monoSet_ge_card_sub_one_completeGraph (n := n) (A := A) hn4
    omega
  · have hne3 : n = 3 := by omega
    subst hne3
    rintro ⟨A, hA⟩
    have h1 := card_monoSet_pos_of_not_isBipartite (G := SimpleGraph.completeGraph (Fin 3))
      (A := A) not_isBipartite_completeGraph_three
    omega

/-- **`JSP90.MaxCutMonoLe c` IS FALSE FOR EVERY `c`** — the maximum-cut certificate cannot prove
Erdős #73, not even with a constant that is allowed to depend on nothing at all.  The witness is
`K_{c + 2}` (for `c ≥ 1`) and `K_3` (for `c = 0`): these satisfy `LocIndep c`, their optimal odd
cycle transversal number is `c` (`JSP90.closeToBipartite_iff_completeGraph_add_two`), and *every*
cut certifies at least `c + 1` vertices. -/
theorem not_maxCutMonoLe (c : ℕ) : ¬ MaxCutMonoLe.{0} c := by
  intro h
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : ∃ A : Finset (Fin 3),
        StableCut (SimpleGraph.completeGraph (Fin 3)) A ∧
          (MonoSet (SimpleGraph.completeGraph (Fin 3)) A).card ≤ 0 := by
      exact h (Fin 3) (inferInstance) (SimpleGraph.completeGraph (Fin 3)) 1 (completeGraph_locIndep 1)
    obtain ⟨A, _, hcard⟩ := h1
    have hnb := card_monoSet_pos_of_not_isBipartite (G := SimpleGraph.completeGraph (Fin 3))
      (A := A) not_isBipartite_completeGraph_three
    omega
  · have hc1 : 1 ≤ c := by omega
    have hn3 : 3 ≤ c + 2 := by
      have h2 : 2 ≤ c + 1 := Nat.succ_le_succ hc1
      exact Nat.succ_le_succ h2
    have h1 : ∃ A : Finset (Fin (c + 2)),
        StableCut (SimpleGraph.completeGraph (Fin (c + 2))) A ∧
          (MonoSet (SimpleGraph.completeGraph (Fin (c + 2))) A).card ≤ c := by
      exact h (Fin (c + 2)) (inferInstance) (SimpleGraph.completeGraph (Fin (c + 2))) c
        (completeGraph_locIndep c)
    obtain ⟨A, _, hcard⟩ := h1
    exact not_exists_monoCard_le_completeGraph (n := c + 2) (c := c) (hn := hn3)
      (hc := by omega) ⟨A, hcard⟩

/-- **`JSP90.MaxCutOfMonoCardLe c` IS FALSE FOR EVERY `c`** as well: "maximum cut" and "stable cut"
are interchangeable (`JSP90.stableCut_of_isMaxCut`), so the two routes fail together. -/
theorem not_maxCutOfMonoCardLe (c : ℕ) : ¬ MaxCutOfMonoCardLe.{0} c := by
  intro h
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : ∃ A : Finset (Fin 3),
        IsMaxCut (SimpleGraph.completeGraph (Fin 3)) A ∧
          (MonoSet (SimpleGraph.completeGraph (Fin 3)) A).card ≤ 0 := by
      exact h (Fin 3) (inferInstance) (SimpleGraph.completeGraph (Fin 3)) 1 (completeGraph_locIndep 1)
    obtain ⟨A, _, hcard⟩ := h1
    have hnb := card_monoSet_pos_of_not_isBipartite (G := SimpleGraph.completeGraph (Fin 3))
      (A := A) not_isBipartite_completeGraph_three
    omega
  · have hc1 : 1 ≤ c := by omega
    have hn3 : 3 ≤ c + 2 := by
      have h2 : 2 ≤ c + 1 := Nat.succ_le_succ hc1
      exact Nat.succ_le_succ h2
    have h1 : ∃ A : Finset (Fin (c + 2)),
        IsMaxCut (SimpleGraph.completeGraph (Fin (c + 2))) A ∧
          (MonoSet (SimpleGraph.completeGraph (Fin (c + 2))) A).card ≤ c := by
      exact h (Fin (c + 2)) (inferInstance) (SimpleGraph.completeGraph (Fin (c + 2))) c
        (completeGraph_locIndep c)
    obtain ⟨A, _, hcard⟩ := h1
    exact not_exists_monoCard_le_completeGraph (n := c + 2) (c := c) (hn := hn3)
      (hc := by omega) ⟨A, hcard⟩

end

end JSP90
