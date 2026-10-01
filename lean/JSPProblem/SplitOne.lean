/-
# JSP-000090 — charging ONE vertex of a 2-cut, not two

`JSPProblem/Separator.lean` decomposes `G` along a 2-cut `{a, b}` and reduces the odd cycle
transversal of `G` to the transversals of the pieces `T_i ∪ {a, b}`, at the price of the two
vertices of the cut:

```
τ(G)  ≤  2 + Σ_i τ(T_i ∪ {a,b})                (JSP90.VertexSplit.exists_transversal)
CloseToBipartite (m * t + 2) G                   (JSP90.erdos73On_of_split)
```

Its header names the missing step exactly:

> the two vertices of the cut are charged in full (`+ 2`), whereas the sharp step would charge
> only **one** of them (that needs the "*a cycle meeting exactly one vertex of the cut lies in a
> piece*" companion of `cycle_subset_parts`)

This file is that companion and the sharp step.  It is a fifth independent attack family, on the
**granularity of the separator**, not on the class of graphs.

## What is proved

**Part 1 — the missing structural lemma.**  `VertexSplit.cycle_subset_insert`: an odd cycle which
contains `a` and **avoids** `b` lies in `T_i ∪ {a}` for a single `i`.  The reason is that `C \ {a}`
is a *path* whose vertices avoid `{a, b}`, and no edge joins two distinct parts, so the whole path
lies in one part.  Consequently

* `VertexSplit.oddCycle_piece_or_both` — **the only odd cycles of `G` that are not contained in a
  piece are the ones containing *both* `a` and `b`**.  This *strengthens* the existing
  `VertexSplit.oddCycle_piece_or_avoid` (which only says "or meets the cut"): a cycle meeting the
  cut in one vertex only is still contained in a piece.  The symmetry of the cut is taken from
  `JSPProblem/Count.lean`'s `VertexSplit.swap`.

**Part 2 — the sharp cut step.**  `VertexSplit.hitsOddCycles_one` and
`VertexSplit.exists_transversal_one`: a transversal of every piece, together with the **single**
vertex `a`, is a transversal of `G`:

```
τ(G)  ≤  1 + Σ_i τ(T_i ∪ {a,b})                (strictly better than  2 + Σ_i τ(T_i ∪ {a,b}))
```

**Part 3 — new instances of the headline theorem.**

* `erdos73On_of_split_one` — `CloseToBipartite (1 + m * t) G` instead of `(m * t + 2) G`.
* `erdos73On_of_split_one_of_bounded_branch` — `CloseToBipartite (1 + (m + k) * t) G` instead of
  `(2 + (m + k) * t) G`.
* `closeToBipartite_of_split_one_of_oddCycleErdosPosa` — the **Erdős–Pósa form**: the odd cycle
  packing bound restricts to the pieces (`packing_le_of_split`), and the pieces' transversal
  bounds combine with **one** cut vertex, with the constant `1 + m * t`.  This is the step an
  induction on the Erdős–Pósa function along a 2-cut decomposition actually needs, and it is
  strictly stronger than the `+ 2` bookkeeping it replaces.

**Part 4 — the `+1` is necessary.**  `sp5` is a concrete 2-cut of the 5-cycle `c5` whose two
pieces are *both bipartite* (odd cycle transversal number `0`) while `c5` is not bipartite: so no
transversal of size `0` exists, and the constant `1 + m * t` of Parts 2–3 cannot be lowered to
`m * t`.  The obstruction living across the cut is real, and one cut vertex is exactly what it
costs.

## What this does not give

The `+1` is a per-decomposition constant, not a function of `k`: this sharpens the reduction, it
does not close it.  Behind `jsp_000090_main` stands `JSP90.OddCycleErdosPosa r` for the graphs with
no 2-cut at all, i.e. the 3-connected case, where the classical proof needs Mader's structure
theorem at a shortest odd cycle and a Menger-type fan lemma.  See `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.Separator
import JSPProblem.Count

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqSplitOne : DecidableEq V := Classical.decEq V

/-! ### Part 1 — a cycle meeting ONE vertex of the cut lies in a piece -/

section OneVertex

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **THE MISSING STRUCTURAL LEMMA: an odd cycle which contains `a` and avoids `b` lies in one
part, together with `a`.**

The cycle minus `a` is a path, and every vertex of it avoids `{a, b}`; since no edge joins two
distinct parts, the whole path lies in one part.  The proof runs a propagation lemma (`hrun` below) twice — once over the
vertices *before* `a` in the cyclic order and once over the vertices *after* `a` — and joins the two
runs at the vertex just before `a`, which the second run meets again one turn later. -/
theorem VertexSplit.cycle_subset_insert {C : Finset V} (hC : IsOddCycle G C) (ha : a ∈ C)
    (hb : b ∉ C) : ∃ i : Fin t, C ⊆ insert a (sp.parts i) := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < 3) hm3
  let mk : ℕ → Fin m := fun s => ⟨s % m, Nat.mod_lt _ (by omega)⟩
  have hmod : ∀ s : ℕ, (s % m + 1) % m = (s + 1) % m := by
    intro s
    calc (s % m + 1) % m
        = ((s % m + 1) + m * (s / m)) % m := by rw [Nat.add_mul_mod_self_left]
      _ = (s + 1) % m := by
          have h2 : (s % m + 1) + m * (s / m) = s + 1 := by
            have h3 := Nat.mod_add_div s m
            omega
          rw [h2]
  have hstep : ∀ s : ℕ, G.Adj (f (mk s)) (f (mk (s + 1))) := by
    intro s
    have h := hcyc (mk s)
    have hval : (s % m + 1) % m = (s + 1) % m := hmod s
    have heq : f (cycSucc (mk s)) = f (mk (s + 1)) := congrArg f (Fin.ext hval)
    rw [heq] at h
    exact h
  have hmk : ∀ p q : ℕ, p % m = q % m → mk p = mk q := by
    intro p q h
    exact Fin.ext h
  have hmk_wrap : ∀ q : ℕ, q < m → mk (q + m) = mk q := by
    intro q hq
    refine Fin.ext ?_
    show (q + m) % m = q % m
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  have hmemC : ∀ s : ℕ, f (mk s) ∈ C := fun s => (hCmem (f (mk s))).mpr ⟨mk s, rfl⟩
  have hfb : ∀ s : ℕ, f (mk s) ≠ b := fun s hcon => hb (hcon ▸ hmemC s)
  obtain ⟨j₀, hj₀⟩ := (hCmem a).mp ha
  have ha₀ : f (mk j₀.val) = a := by
    have hval : mk j₀.val = j₀ := Fin.ext (Nat.mod_eq_of_lt j₀.isLt)
    rw [hval]
    exact hj₀
  have hkey : ∀ s : ℕ, f (mk s) = a ↔ s % m = j₀.val := by
    intro s
    constructor
    · intro h
      have hval : s % m = j₀.val % m := by
        have : mk s = mk j₀.val := hinj (h ▸ ha₀.symm)
        exact congrArg Fin.val this
      rw [Nat.mod_eq_of_lt j₀.isLt] at hval
      exact hval
    · intro h
      have hval : mk s = mk j₀.val := hmk s j₀.val
        (by rw [Nat.mod_eq_of_lt j₀.isLt]; exact h)
      exact (congrArg f hval).trans ha₀
  -- the vertices of the cycle equal to `a` are exactly the indices congruent to `j₀.val`
  have hnoa : ∀ s : ℕ, s < j₀.val → s < m → ¬ (s % m = j₀.val) := by
    intro s hs1 hs2 h
    rw [Nat.mod_eq_of_lt hs2] at h
    omega
  have hnoa' : ∀ s : ℕ, j₀.val < s → s < j₀.val + m → ¬ (s % m = j₀.val) := by
    intro s hs1 hs2 h
    rcases lt_or_ge s m with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · have hne0 : s / m ≠ 0 := by
        intro hc
        rcases Nat.div_eq_zero_iff.mp hc with hm | hlt
        · exact absurd hm (Nat.ne_of_gt hmpos)
        · exact absurd hlt (Nat.not_lt_of_ge hge)
      have hmul : m ≤ m * (s / m) := by
        simpa using Nat.mul_le_mul_left m (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne0))
      have h3 := Nat.mod_add_div s m
      omega
  -- the two runs of the propagation
  have hrun : ∀ (i : Fin t) (lo hi : ℕ) (hlo : f (mk lo) ∈ sp.parts i)
      (hna : ∀ s : ℕ, lo ≤ s → s ≤ hi → f (mk s) ≠ a),
      ∀ s : ℕ, lo ≤ s → s ≤ hi → f (mk s) ∈ sp.parts i := by
    intro i lo hi hlo hna s hs1 hs2
    induction s using Nat.strong_induction_on with
    | _ s ih =>
        by_cases hs : s = lo
        · rw [hs]
          exact hlo
        · by_cases hs' : s = lo + 1
          · have hval : mk (lo + 1) = mk s := by congr 1; omega
            rw [← hval]
            exact sp.mem_part_of_adj (hstep lo) hlo (hna lo (by omega) (by omega)) (hfb lo)
              (hna (lo + 1) (by omega) (by omega)) (hfb (lo + 1))
          · have hsp : lo + 1 < s := by omega
            have hne' : f (mk (s - 1)) ≠ a := hna (s - 1) (by omega) (by omega)
            have hval : mk ((s - 1) + 1) = mk s := by congr 1; omega
            have hadj := hstep (s - 1)
            rw [hval] at hadj
            exact sp.mem_part_of_adj hadj (ih (s - 1) (by omega) (by omega) (by omega)) hne'
              (hfb (s - 1)) (hna s hs1 hs2) (hfb s)
  have hmain : ∃ i : Fin t, ∀ s : ℕ, s ≠ j₀.val → s < m → f (mk s) ∈ sp.parts i := by
    by_cases ht₀ : j₀.val = 0
    · -- `a` is the first vertex: one run, over the whole rest of the cycle
      obtain ⟨i₀, hi₀⟩ := sp.mem_parts_of_not_mem_cut (f (mk 1))
        (fun hcon => hnoa' 1 (by omega) (by omega) ((hkey 1).mp hcon)) (hfb 1)
      refine ⟨i₀, fun s hs hs2 => ?_⟩
      exact hrun i₀ 1 (m - 1) hi₀
        (fun u hu1 hu2 hcon => hnoa' u (by omega) (by omega) ((hkey u).mp hcon)) s (by omega)
        (by omega)
    · -- `a` is in the interior: two runs, joined just before `a`
      obtain ⟨iA, hiA⟩ := sp.mem_parts_of_not_mem_cut (f (mk 0))
        (fun hcon => hnoa 0 (by omega) (by omega) ((hkey 0).mp hcon)) (hfb 0)
      obtain ⟨iB, hiB⟩ := sp.mem_parts_of_not_mem_cut (f (mk (j₀.val + 1)))
        (fun hcon => hnoa' (j₀.val + 1) (by omega) (by omega) ((hkey (j₀.val + 1)).mp hcon))
        (hfb (j₀.val + 1))
      have hnaA : ∀ s : ℕ, 0 ≤ s → s ≤ j₀.val - 1 → f (mk s) ≠ a := by
        intro s hs0 hs hcon
        exact hnoa s (by omega) (by omega) ((hkey s).mp hcon)
      have hnaB : ∀ s : ℕ, j₀.val + 1 ≤ s → s ≤ j₀.val + m - 1 → f (mk s) ≠ a := by
        intro s hs0 hs hcon
        exact hnoa' s (by omega) (by omega) ((hkey s).mp hcon)
      have hmk' : mk (j₀.val + m - 1) = mk (j₀.val - 1) := by
        have h1 : j₀.val + m - 1 = (j₀.val - 1) + m := by omega
        rw [h1]
        exact hmk_wrap (j₀.val - 1) (by omega)
      have heq : f (mk (j₀.val - 1)) = f (mk (j₀.val + m - 1)) := (congrArg f hmk').symm
      have hmemA : f (mk (j₀.val - 1)) ∈ sp.parts iA :=
        hrun iA 0 (j₀.val - 1) hiA hnaA (j₀.val - 1) (by omega) (by omega)
      have hmemB : f (mk (j₀.val - 1)) ∈ sp.parts iB := by
        have h := hrun iB (j₀.val + 1) (j₀.val + m - 1) hiB hnaB (j₀.val + m - 1) (by omega)
          (by omega)
        rwa [← heq] at h
      have hjoin : iA = iB := by
        by_contra hne
        have hy : f (mk (j₀.val - 1)) ∈ sp.parts iA ∩ sp.parts iB :=
          Finset.mem_inter.mpr ⟨hmemA, hmemB⟩
        rw [sp.hdisj iA iB hne] at hy
        exact absurd hy (by simp)
      refine ⟨iB, fun s hs hs2 => ?_⟩
      rcases lt_or_gt_of_ne hs with hlt | hgt
      · exact hjoin ▸ hrun iA 0 (j₀.val - 1) hiA hnaA s (by omega) (by omega)
      · exact hrun iB (j₀.val + 1) (j₀.val + m - 1) hiB hnaB s (by omega) (by omega)
  obtain ⟨i, hi⟩ := hmain
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  have hval : mk j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  by_cases hj₀ : j.val = j₀.val
  · refine Finset.mem_insert.mpr (Or.inl ?_)
    have h1 : x = f (mk j.val) := hj.symm.trans (congrArg f hval).symm
    have h2 : f (mk j.val) = a := (congrArg f (hmk j.val j₀.val (by rw [hj₀]))).trans ha₀
    exact h1.trans h2
  · refine Finset.mem_insert.mpr (Or.inr ?_)
    have h1 : x = f (mk j.val) := hj.symm.trans (congrArg f hval).symm
    rw [h1]
    exact hi j.val hj₀ j.isLt

end OneVertex

/-! ### Part 1b — the strengthened statement about odd cycles and pieces -/

section Cycles

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **A STRENGTHENING OF `JSPProblem/Separator.lean`'s `VertexSplit.oddCycle_piece_or_avoid`: every
odd cycle of `G` is contained in a piece unless it contains *both* vertices of the cut.**

The `+2` charged by `JSPProblem.VertexSplit.exists_transversal` exists only because that lemma
allowed an odd cycle to meet the cut in a *single* vertex.  Part 1 shows that such a cycle is
contained in a piece after all, so only the cycles meeting the cut in **both** vertices are left
over. -/
theorem VertexSplit.oddCycle_piece_or_both {C : Finset V} (hC : IsOddCycle G C) :
    (∃ i : Fin t, C ⊆ sp.piece i) ∨ ({a, b} : Finset V) ⊆ C := by
  have hmemab : ∀ x : V, x ∈ ({a, b} : Finset V) → x = a ∨ x = b := by
    intro x hx
    exact (Finset.mem_insert.mp hx).elim Or.inl fun h => Or.inr (Finset.mem_singleton.mp h)
  by_cases ha : a ∈ C
  · by_cases hb : b ∈ C
    · refine Or.inr (fun x hx => ?_)
      rcases hmemab x hx with h | h
      · rw [h]
        exact ha
      · rw [h]
        exact hb
    · obtain ⟨i, hi⟩ := sp.cycle_subset_insert hC ha hb
      refine Or.inl ⟨i, fun x hx => (sp.mem_piece i x).mpr ?_⟩
      rcases Finset.mem_insert.mp (hi hx) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · by_cases hb : b ∈ C
    · obtain ⟨i, hi⟩ := sp.swap.cycle_subset_insert hC hb ha
      refine Or.inl ⟨i, fun x hx => (sp.mem_piece i x).mpr ?_⟩
      rcases Finset.mem_insert.mp (hi hx) with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have hcut : C ∩ ({a, b} : Finset V) = ∅ := by
        ext x
        constructor
        · intro him
          rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at him
          rcases him with ⟨hxc, hx | hx⟩
          · exact absurd (hx ▸ hxc) ha
          · exact absurd (hx ▸ hxc) hb
        · intro hx
          exact absurd hx (by simp)
      obtain ⟨i, hi⟩ := sp.cycle_subset_parts hC hcut
      refine Or.inl ⟨i, fun x hx => (sp.mem_piece i x).mpr (Or.inr (Or.inr (hi hx)))⟩

end Cycles

/-! ### Part 2 — charging ONE vertex of the cut -/

section TransversalOne

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **THE SHARP CUT STEP: a transversal of every piece, together with the SINGLE vertex `a`, is an
odd cycle transversal of `G`.**

Indeed, an odd cycle of `G` avoiding `a` is contained in a piece by
`VertexSplit.oddCycle_piece_or_both`, hence is an odd cycle of that piece and is met by the
transversal of that piece.  This replaces `VertexSplit.hitsOddCycles`, which needs `a` **and** `b`. -/
theorem VertexSplit.hitsOddCycles_one [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (sp.piece i)) (X i)) :
    HitsOddCycles G (insert a (Finset.biUnion Finset.univ X)) := by
  intro C hC
  by_contra hcon
  have ha : a ∉ C := by
    intro ha'
    have him : a ∈ C ∩ insert a (Finset.biUnion Finset.univ X) :=
      Finset.mem_inter.mpr ⟨ha', Finset.mem_insert_self a _⟩
    rw [hcon] at him
    exact absurd him (by simp)
  rcases sp.oddCycle_piece_or_both hC with ⟨i, hsub⟩ | hboth
  · have hC' : IsOddCycle (induceFinset G (sp.piece i)) C := hC.induceFinset hsub
    have hne : (C ∩ X i).Nonempty := Finset.nonempty_iff_ne_empty.mpr (hhits i C hC')
    obtain ⟨x, hx⟩ := hne
    have hxC : x ∈ C := (Finset.mem_inter.mp hx).1
    have hxX : x ∈ X i := (Finset.mem_inter.mp hx).2
    have him : x ∈ C ∩ insert a (Finset.biUnion Finset.univ X) := Finset.mem_inter.mpr ⟨hxC,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxX⟩))⟩
    rw [hcon] at him
    exact absurd him (by simp)
  · exact ha (hboth (Finset.mem_insert_self a ({b} : Finset V)))

/-- **A 2-cut decomposition of odd cycle transversals, charging ONE vertex of the cut.**  If each
piece `T_i ∪ {a,b}` has an odd cycle transversal of at most `m` vertices, then `G` has an odd cycle
transversal of at most `1 + m * t` vertices.  This is **strictly better** than the `2 + m * t` of
`VertexSplit.exists_transversal` (round 78). -/
theorem VertexSplit.exists_transversal_one [Fintype V] {m : ℕ} (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (sp.piece i)) (X i))
    (hcard : ∀ i : Fin t, (X i).card ≤ m) :
    ∃ Y : Finset V, HitsOddCycles G Y ∧ Y.card ≤ 1 + m * t := by
  refine ⟨insert a (Finset.biUnion Finset.univ X), sp.hitsOddCycles_one X hhits, ?_⟩
  have hle : (insert a (Finset.biUnion Finset.univ X) : Finset V).card
      ≤ (Finset.biUnion Finset.univ X).card + 1 := Finset.card_insert_le a _
  have h2 : (Finset.biUnion Finset.univ X).card ≤ ∑ i : Fin t, (X i).card :=
    Finset.card_biUnion_le
  have h3 : (∑ i : Fin t, (X i).card) ≤ ∑ _i : Fin t, (m : ℕ) :=
    Finset.sum_le_sum fun i hi => hcard i
  have h4 : (∑ _i : Fin t, (m : ℕ)) = m * t := by
    calc (∑ _i : Fin t, (m : ℕ)) = (Finset.univ : Finset (Fin t)).card * m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rfl
      _ = m * t := by rw [Finset.card_fin, Nat.mul_comm]
  have h5 : (Finset.biUnion Finset.univ X).card ≤ m * t :=
    h2.trans (h3.trans (le_of_eq h4))
  omega

end TransversalOne

/-! ### Part 3 — new instances of the headline theorem -/

section Instances

universe u

variable {a b : V} {t : ℕ}

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, AND A STRICT IMPROVEMENT OF ROUND 78'S.**  Suppose
`V(G)` splits as `{a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete, and Erdős's local
hypothesis forces `CloseToBipartite m` in each of the pieces `T_i ∪ {a,b}` (which is what an
induction on the Erdős–Pósa function needs).  Then `LocIndep k G` forces
`CloseToBipartite (1 + m * t) G`: the transversals of the pieces, together with the **single**
vertex `a` of the cut, are a transversal of `G`.

`JSPProblem.erdos73On_of_split` gives `CloseToBipartite (m * t + 2) G` from the same hypotheses;
this theorem improves the constant by one, so it is a strictly stronger instance. -/
theorem erdos73On_of_split_one (k m t : ℕ) {W : Type u} [Fintype W] (G : SimpleGraph W)
    (a b : W) (sp : VertexSplit G a b t)
    (hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) →
      CloseToBipartite m (induceFinset G (sp.piece i)))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * t) G := by
  have hLoc : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) :=
    fun i => hG.of_induceFinset (sp.piece i)
  obtain ⟨X, hX, hhits⟩ := sp.exists_transversal_one (m := m)
    (X := fun i => Classical.choose (hpiece i (hLoc i)))
    (fun i => hitsOddCycles_of_isBipartite_delete ((hpiece i (hLoc i)).choose_spec.2))
    (fun i => (hpiece i (hLoc i)).choose_spec.1)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * t)).mpr
    ⟨X, by omega, hX⟩

/-- **The improvement is genuine**: the constant of `erdos73On_of_split_one` is strictly below the
constant of `erdos73On_of_split` for every `m, t`. -/
theorem one_add_mul_lt_add_two_add_mul (m t : ℕ) : 1 + m * t < m * t + 2 + (0 : ℕ) := by omega

/-- **THE ERDŐS–PÓSA FORM OF THE SHARP CUT STEP.**  Suppose every odd cycle packing of `G` has at
most `r` members, and that on each piece the packing hypothesis forces `CloseToBipartite m`.  Then
`G` is the union of a bipartite graph and at most `1 + m * t` vertices.

This is the form in which the sharp cut step is used in the Erdős–Pósa proof: the packing
hypothesis restricts to the pieces by `VertexSplit.packing_le_of_split`, and the conclusion pays for
**one** vertex of the cut.  With round 78's `VertexSplit.exists_transversal` the same induction
would have to pay for two. -/
theorem closeToBipartite_of_split_one_of_oddCycleErdosPosa (r m t : ℕ) {W : Type u} [Fintype W]
    (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hpiece : ∀ i : Fin t,
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := induceFinset G (sp.piece i)) C →
        C.card ≤ r) → CloseToBipartite m (induceFinset G (sp.piece i)))
    (hpack : ∀ C : Finset (Finset W), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (1 + m * t) G := by
  obtain ⟨X, hX, hhits⟩ := sp.exists_transversal_one (m := m)
    (X := fun i => (hpiece i (fun C hC => packing_le_of_split sp hpack i hC)).choose)
    (fun i => hitsOddCycles_of_isBipartite_delete
      ((hpiece i (fun C hC => packing_le_of_split sp hpack i hC)).choose_spec.2))
    (fun i => (hpiece i (fun C hC => packing_le_of_split sp hpack i hC)).choose_spec.1)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * t)).mpr
    ⟨X, by omega, hX⟩

/-- **A second new instance of the headline theorem: the branch-vertex instance across a 2-cut, with
the sharp constant.**  Round 78's `erdos73On_of_split_of_bounded_branch` gives
`CloseToBipartite (2 + (m + k) * t) G`; here the two vertices of the cut cost **one**. -/
theorem erdos73On_of_split_one_of_bounded_branch (k m t : ℕ) {W : Type u} [Fintype W]
    (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hB : ∀ i : Fin t, ∃ B : Finset W, B ⊆ sp.piece i ∧ B.card ≤ m ∧
      ∀ v : W, BranchVertex (induceFinset G (sp.piece i)) v → v ∈ B)
    (hG : LocIndep k G) : CloseToBipartite (1 + (m + k) * t) G := by
  have hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) →
      CloseToBipartite (m + k) (induceFinset G (sp.piece i)) := by
    intro i hLoc
    obtain ⟨B, -, hBcard, hBall⟩ := hB i
    exact erdos73On_of_few_high_degree (k := k) (m := m) W (inferInstance : Fintype W)
      (induceFinset G (sp.piece i)) hLoc B hBall hBcard
  exact erdos73On_of_split_one (k := k) (m := m + k) (t := t) G a b sp hpiece hG

end Instances

/-! ### Part 4 — the `+1` is necessary: the 5-cycle -/

section Sharpness

/-- **The cycle `0 - 1 - 2 - 3 - 4 - 0` on `Fin 5`.** -/
def c5 : SimpleGraph (Fin 5) where
  Adj u w := (u.val + 1) % 5 = w.val ∨ (w.val + 1) % 5 = u.val
  symm := ⟨fun u w h => h.elim (fun h1 => Or.inr h1) fun h2 => Or.inl h2⟩
  loopless := ⟨fun u h =>
    h.elim (fun h1 => by omega) fun h2 => by omega⟩

@[simp] theorem c5_adj {u w : Fin 5} :
    c5.Adj u w ↔ (u.val + 1) % 5 = w.val ∨ (w.val + 1) % 5 = u.val := Iff.rfl

/-- **A 2-cut of `c5` at the two vertices `0` and `2`, whose two pieces are the paths `0 - 1 - 2`
and `2 - 3 - 4 - 0`.**  Both pieces are bipartite and `c5` is not, so a transversal of the pieces
does not suffice: one vertex of the cut has to be paid for. -/
def sp5 : VertexSplit c5 0 2 2 where
  parts := fun i => if i.val = 0 then ({1} : Finset (Fin 5)) else ({3, 4} : Finset (Fin 5))
  hne := by
    intro i
    fin_cases i <;> simp
  hdisj := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  hcov := by
    intro x
    fin_cases x <;> simp
  hanti := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals (rcases ‹_ ∨ _› with h' | h' <;> simp_all [c5_adj])
  hnadj := by simp [c5_adj]

/-- **The whole 5-cycle is an odd cycle of `c5`**, so `c5` is not bipartite. -/
theorem exists_isOddCycle_c5 : ∃ s : Finset (Fin 5), IsOddCycle c5 s :=
  ⟨_, isOddCycle_image (H := c5) (m := 5) (fun j => j) (by decide) (by omega) (fun _ _ h => h)
    (fun j => Or.inl (cycSucc_val j).symm)⟩

/-- **`c5` is not bipartite**, a machine-checked witness that the two vertices of a 2-cut cannot
both be spared. -/
theorem not_isBipartite_c5 : ¬ c5.IsBipartite := by
  rintro h
  exact not_isOddCycle_of_isBipartite h exists_isOddCycle_c5

/-- **... and it needs at least one vertex deleted.** -/
theorem not_closeToBipartite_zero_c5 : ¬ CloseToBipartite 0 c5 := by
  rintro ⟨X, hX, hb⟩
  have hX' : X = ∅ := Finset.card_eq_zero.mp (by omega)
  rw [hX', deleteFinset_empty] at hb
  exact not_isBipartite_c5 hb

/-- **A `Fin 2` colouring of `Fin 5` alternating along the path `1 - 2 - 3 - 4`** (so that
`c5 - {0}` is bipartite). -/
def colPath1 : Fin 5 → Fin 2 := fun u => ⟨(u.val + 1) % 2, Nat.mod_lt _ (by decide)⟩

/-- **A `Fin 2` colouring of `Fin 5` alternating along the path `0 - 4 - 3 - 2`** (so that the
piece `{0, 2, 3, 4}` is bipartite). -/
def colPath2 : Fin 5 → Fin 2 := fun u => ⟨((5 - u.val) % 5) % 2, Nat.mod_lt _ (by decide)⟩

/-- **A `Fin 2` colouring of `Fin 5` alternating along the path `0 - 1 - 2`** (so that the piece
`{0, 1, 2}` is bipartite). -/
def colPath3 : Fin 5 → Fin 2 := fun u => ⟨u.val % 2, Nat.mod_lt _ (by decide)⟩

/-- **Both pieces of `sp5` are bipartite**: their odd cycle transversal number is `0`. -/
theorem isBipartite_piece5 : ∀ i : Fin 2, (induceFinset c5 (sp5.piece i)).IsBipartite := by
  intro i
  fin_cases i
  · refine ⟨colPath3, ?_⟩
    intro u v hadj
    simp only [induce_adj] at hadj
    fin_cases u <;> fin_cases v <;> simp_all [colPath3, sp5, c5_adj]
  · refine ⟨colPath2, ?_⟩
    intro u v hadj
    simp only [induce_adj] at hadj
    fin_cases u <;> fin_cases v <;> simp_all [colPath2, sp5, c5_adj]

/-- **THE `+1` IS NECESSARY.**  In the 2-cut `sp5` of the 5-cycle both pieces need no deletion at
all (`isBipartite_piece5`), yet `c5` does, so the constant of
`JSPProblem.VertexSplit.exists_transversal_one` cannot be lowered from `1 + m * t` to `m * t`. -/
theorem split_one_constant_necessary :
    (∀ i : Fin 2, (induceFinset c5 (sp5.piece i)).IsBipartite) ∧ ¬ CloseToBipartite 0 c5 :=
  ⟨isBipartite_piece5, not_closeToBipartite_zero_c5⟩

/-- **THE NEW STEP IS NON-VACUOUS AND ITS CONSTANT IS ATTAINED ON A REAL GRAPH.**  Both pieces of the
2-cut `sp5` have odd cycle transversal number `0`, so `∅` is a transversal of each of them, and the
sharp cut step `VertexSplit.exists_transversal_one` produces a transversal of `c5` of size at most
`1 + 0 * 2 = 1`, while `not_closeToBipartite_zero_c5` shows none of size `0` exists.  So the round-78
bound `2 + m * t` is off by exactly one vertex on this example, and the new bound `1 + m * t` is
optimal. -/
theorem sp5_split_one_attained :
    (∃ Y : Finset (Fin 5), HitsOddCycles c5 Y ∧ Y.card ≤ 1 + 0 * 2) ∧ ¬ CloseToBipartite 0 c5 := by
  refine ⟨sp5.exists_transversal_one (m := 0) (X := fun _ => ∅)
      (fun i C hC =>
        False.elim ((not_isOddCycle_of_isBipartite (isBipartite_piece5 i)) ⟨C, hC⟩))
      (fun i => by simp), not_closeToBipartite_zero_c5⟩

/-- **And the sharp constant is attained**: deleting the single vertex `0` makes `c5` bipartite, so
`1 + 0 * 2` is exactly the value of `erdos73On_of_split_one` on this split and is optimal. -/
theorem closeToBipartite_one_c5 : CloseToBipartite 1 c5 := by
  refine ⟨{0}, by decide, ?_⟩
  refine ⟨colPath1, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  fin_cases u <;> fin_cases v <;> simp_all [colPath1, c5_adj]

end Sharpness

end

end JSP90
