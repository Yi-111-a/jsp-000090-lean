/-
# JSP-000090 — a shortest odd cycle is induced, and the local structure of `G` at it

`JSPProblem/Fan.lean` developed the arc machinery of the classical fan argument: the two arcs
between two vertices of an odd cycle have **opposite** parity, so closing the odd one through a
vertex gives a *simple odd cycle* (`arc_isOddCycle`), which yields the fan lemma and the short-arc
lemma at a shortest odd cycle.

That machinery has one limitation which this file removes.  In `JSPProblem/Fan.lean` the vertex
closing an arc must lie **outside the whole cycle** (`hxC : x ∉ C`), so the machinery says nothing
about **chords**, i.e. about the edges *inside* a shortest odd cycle.  The three lemmas below
generalise the arc constructor to a closing vertex which merely avoids the **arc itself**
(`hximg : ∀ t ≤ d, f (cycSucc^[t] i) ≠ x`), which is exactly what a chord provides: the chord
between `f i` and `f (cycSucc^[d] i)` closes the arc `i → cycSucc^[d] i` through the vertex
`f (cycSucc^[d] i)`, which lies *on* the cycle.

The consequence is the structural fact that the classical argument needs at the base of every
induction:

* `no_chord_of_shortest_oddCycle` — **a shortest odd cycle of `G` is chordless**: for two distinct
  vertices `a`, `b` of its cyclic numbering which are not consecutive around the cycle, `f a` and
  `f b` are not adjacent.  (A chord splits the cycle into two cycles of `d + 1` and `m - d + 1`
  vertices; their lengths add up to the odd number `m + 2`, so exactly one of them is odd, and that
  one has at most `m - 1` vertices, contradicting the minimality of `C`.)
* `induceFinset_adj_of_shortest` — consequently **the subgraph induced by a shortest odd cycle is
  exactly that cycle**: `(induceFinset G C).Adj (f a) (f b) ↔ a = cycSucc b ∨ b = cycSucc a`.
* `exists_shortest_oddCycle` / `isInduced_shortest_oddCycle` — a shortest odd cycle exists whenever
  `G` has an odd cycle, and it is induced.

Together with `JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` (every vertex outside a
shortest odd cycle of length `≥ 5` meets it in at most two vertices, exactly two steps apart) this
gives the *complete* local picture at a shortest odd cycle: inside, the cycle and nothing else;
outside, every vertex is attached through a single short arc.
-/

import JSPProblem.Residue
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-! ### The arc constructor, with a closing vertex on the cycle -/

/-- **The arc-closed walk is a simple cycle, even if the closing vertex lies on the cycle.**
Here it is enough that `x` differs from the `t` steps-after-`i` vertices for `t ≤ d`, i.e. from the
whole arc `i, cycSucc i, …, cycSucc^[d] i`; this is the hypothesis a **chord** provides.  The
statement `JSP90.arcFun_inj` of `JSPProblem/Fan.lean` is the special case `x ∉ C`. -/
theorem arcFun_inj_of_notMem {m d : ℕ} (hdm : d < m) (f : Fin m → V) (hinj : Function.Injective f)
    (i : Fin m) (x : V) (hximg : ∀ t : ℕ, t ≤ d → f ((cycSucc^[t] : Fin m → Fin m) i) ≠ x)
    (a b : Fin (d + 2)) (hne : a ≠ b) :
    arcFun m d f i x a ≠ arcFun m d f i x b := by
  by_cases ha0 : a.val = 0
  · by_cases hb0 : b.val = 0
    · intro hab
      exact hne (Fin.ext (ha0.trans hb0.symm))
    · have hbpos : 0 < b.val := Nat.pos_of_ne_zero hb0
      intro hab
      rw [arcFun, if_pos ha0, arcFun, if_neg hb0] at hab
      exact hximg (b.val - 1) (by omega) hab.symm
  · by_cases hb0 : b.val = 0
    · have hapos : 0 < a.val := Nat.pos_of_ne_zero ha0
      intro hab
      rw [arcFun, if_neg ha0, arcFun, if_pos hb0] at hab
      exact hximg (a.val - 1) (by omega) hab
    · intro hab
      rw [arcFun, if_neg ha0, arcFun, if_neg hb0] at hab
      have hh : ((cycSucc^[a.val - 1] : Fin m → Fin m) i)
          = ((cycSucc^[b.val - 1] : Fin m → Fin m) i) := hinj hab
      have hv : (i.val + (a.val - 1)) % m = (i.val + (b.val - 1)) % m := by
        have h := congrArg Fin.val hh
        simpa only [cycSucc_pow_val] using h
      have hsub : a.val - 1 = b.val - 1 := mod_inj_add (by omega) (by omega) hv
      exact hne (Fin.ext (by omega))

/-- **The arc-closed cycle has exactly `d + 2` vertices**, in the generality of
`arcFun_inj_of_notMem` (so the closing vertex may lie on the cycle). -/
theorem arc_card_of_notMem {m d : ℕ} (hdm : d < m) (f : Fin m → V) (hinj : Function.Injective f)
    (i : Fin m) (x : V) (hximg : ∀ t : ℕ, t ≤ d → f ((cycSucc^[t] : Fin m → Fin m) i) ≠ x) :
    ((Finset.univ : Finset (Fin (d + 2))).image (arcFun m d f i x)).card = d + 2 := by
  have hinjarc : Function.Injective (arcFun m d f i x) := by
    intro a b hab
    by_contra hne
    exact False.elim ((arcFun_inj_of_notMem hdm f hinj i x hximg a b hne) hab)
  rw [Finset.card_image_of_injective]
  · simp
  · exact hinjarc

/-- **Closing an arc through a vertex which is not in the arc gives a simple odd cycle** — the
generalisation of `JSP90.arc_isOddCycle` needed for chords.  As there, if `d` is odd and
`0 < d < m`, the `d + 2` entries `x, f i, f (cycSucc i), …, f (cycSucc^[d-1] i)` are pairwise
distinct and consecutive ones are adjacent, so their image is a simple odd cycle of `d + 2`
vertices. -/
theorem arc_isOddCycle_of_notMem {m d : ℕ} (hm : m % 2 = 1) (hm3 : 3 ≤ m) (f : Fin m → V)
    (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) {i : Fin m}
    (hdm : d < m) (hd0 : 0 < d) {x : V}
    (hximg : ∀ t : ℕ, t ≤ d → f ((cycSucc^[t] : Fin m → Fin m) i) ≠ x)
    (hxi : G.Adj x (f i)) (hlast : G.Adj (f ((cycSucc^[d] : Fin m → Fin m) i)) x)
    (hdodd : d % 2 = 1) :
    IsOddCycle G ((Finset.univ : Finset (Fin (d + 2))).image (arcFun m d f i x)) := by
  have hmod : (d + 2) % 2 = 1 := by
    have h := Nat.mod_add_mod d 2 2
    rw [← h, hdodd]
  have hinjarc : Function.Injective (arcFun m d f i x) := by
    intro a b hab
    by_contra hne
    exact False.elim ((arcFun_inj_of_notMem hdm f hinj i x hximg a b hne) hab)
  refine ⟨d + 2, arcFun m d f i x, hmod, by omega, hinjarc, ?_, ?_⟩
  · exact arcFun_adj hdm hd0 f i x hcyc hxi hlast
  · intro y
    constructor
    · intro hy
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
      exact ⟨j, hj⟩
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **Successive steps around the cycle: `t + 1` steps is one step after `t` steps.** -/
theorem cycSucc_succ_pow (m : ℕ) (i : Fin m) (t : ℕ) :
    ((cycSucc^[t.succ] : Fin m → Fin m) i) = cycSucc ((cycSucc^[t] : Fin m → Fin m) i) :=
  Function.iterate_succ_apply' cycSucc t i

/-- **The cyclic order of an odd cycle has odd length.**  Every cyclic numbering `o` of an odd cycle
`C` has `o.m` odd, because `C` has as many vertices as `o.m` and `o.m` is the length of the odd cycle
witness. -/
theorem cycleOrder_odd {C : Finset V} (hC : IsOddCycle G C) (o : CycleOrder G C) : o.m % 2 = 1 := by
  obtain ⟨m', f', hm', hm3', hinj', hcyc', hmem'⟩ := hC
  have hCcard' : C.card = m' := by
    have heq : C = (Finset.univ : Finset (Fin m')).image f' := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, hmem']
    rw [heq, Finset.card_image_of_injective _ hinj']
    simp
  have hCcard : C.card = o.m := card_eq_cyclicOrder o.f o.hinj o.hmem
  have h1 : o.m % 2 = m' % 2 := by rw [← hCcard, hCcard']
  exact h1.trans hm'

/-! ### Arithmetic of the arc lengths

`omega` does not look through truncated subtraction (`k - 1`, `m - 1 - d`) once a context contains
other such terms, so each of the conversions used below is packaged in its own tiny lemma. -/

theorem lt_of_le_succ_sub_one {t d : ℕ} (h2 : 2 ≤ d) (h : t ≤ d - 1) : t < d := by
  have h1 : t + 1 ≤ d := by omega
  omega

theorem ne_of_le_succ_sub_one {t d : ℕ} (h2 : 2 ≤ d) (h : t ≤ d - 1) : t ≠ d := by
  have h1 : t + 1 ≤ d := by omega
  omega

theorem lt_of_le_sub_succ {t m d : ℕ} (hd0 : 0 < d) (hdm : d < m) (h : t ≤ m - 1 - d) : t < m := by
  have h1 : t + 1 + d ≤ m := by omega
  omega

theorem ne_of_le_sub_succ' {t m d : ℕ} (h1 : t + 1 + d ≤ m) : t ≠ m - d := by
  have h2 : t + 1 ≤ m - d := by omega
  omega

theorem sub_succ_self {d : ℕ} (h : 2 ≤ d) : (d - 1).succ = d := by omega

theorem sub_succ_eq_sub {m d : ℕ} (hdm : d < m) (h : 2 ≤ d) : (m - 1 - d).succ = m - d := by omega

theorem sub_lt_of_two_le {m d : ℕ} (h : 2 ≤ d) (hdm : d < m) : d - 1 < m := by omega

theorem sub_pos_of_two_le {d : ℕ} (h : 2 ≤ d) : 0 < d - 1 := by omega

theorem sub_sub_lt_of_two_le {m d : ℕ} (h1 : 2 ≤ d) (h2 : d ≤ m - 2) : m - 1 - d < m := by
  have h3 : d + 2 ≤ m := by omega
  clear h2
  have h3' : 1 + d ≤ m := by omega
  have h4 : m - (1 + d) < m :=
    (Nat.sub_lt_iff_lt_add (b := 1 + d) (c := m) h3').mpr (Nat.lt_add_of_pos_right (by omega))
  rw [Nat.sub_sub]
  exact h4

theorem sub_sub_pos_of_two_le {m d : ℕ} (h1 : 2 ≤ d) (h2 : d ≤ m - 2) : 0 < m - 1 - d := by
  have h3 : d + 2 ≤ m := by omega
  clear h2
  have h3' : d + 1 < m := by omega
  have h4 : 0 < m - (1 + d) := Nat.sub_pos_iff_lt.mpr (by simpa only [Nat.add_comm] using h3')
  rw [Nat.sub_sub]
  exact h4

theorem absurd_of_le_sub_succ_two {m d : ℕ} (h1 : 2 ≤ d) (h2 : d ≤ m - 2)
    (h3 : m ≤ d - 1 + 2) : False := by
  have h4 : m ≤ d + 1 := by omega
  have h5 : d + 2 ≤ m := by omega
  omega

theorem absurd_of_le_sub_two {m d : ℕ} (h1 : 2 ≤ d) (h2 : d ≤ m - 2)
    (h3 : m ≤ m - 1 - d + 2) : False := by
  have h4 : d ≤ m - 1 := by omega
  omega

theorem sub_lt_self_of_pos {m d : ℕ} (hd0 : 0 < d) (hdm : d < m) : m - d < m := by omega

/-! ### A shortest odd cycle is induced -/

/-- **A shortest odd cycle has no chord.**  Let `C` be an odd cycle of `G` carried by an injective
cyclic numbering `o`, and suppose `C` is of minimum cardinality among the odd cycles of `G`.  If
`a ≠ b` are two of its vertices which are **not** consecutive around the cycle, then `o.f a` and
`o.f b` are **not adjacent**.

Proof.  Suppose `o.f a` and `o.f b` are adjacent, and let `d` be the number of steps around the
cycle from `a` to `b`.  Then `0 < d < m`, and since `b` is neither the successor nor the predecessor
of `a`, `2 ≤ d ≤ m - 2`.  The chord splits the cycle into two cycles, of `d + 1` and `m - d + 1`
vertices; their lengths add up to the odd number `m + 2`, so exactly one of them is odd.  The odd
one is a simple odd cycle of `G` with at most `m - 1 < m` vertices, contradicting the minimality of
`C`.  The two sub-cycles are exactly the two applications of `arc_isOddCycle_of_notMem`: the forward
one closes the arc of `d - 1` steps from `a` through the chord, the backward one closes the arc of
`m - 1 - d` steps from `b`. -/
theorem no_chord_of_shortest_oddCycle {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (o : CycleOrder G C)
    (hm : o.m % 2 = 1) {a b : Fin o.m} (hab : a ≠ b) (hb1 : b ≠ cycSucc a) (hb2 : b ≠ o.prev a) :
    ¬ G.Adj (o.f a) (o.f b) := by
  intro hadj
  obtain ⟨d, hd0, hdm, hdab⟩ := exists_arc (by omega) hab
  -- `d` is neither `1` nor `m - 1`, so `2 ≤ d ≤ m - 2`
  have hdne1 : d ≠ 1 := by
    intro h
    have : cycSucc a = b := by simpa [h] using hdab
    exact hb1 this.symm
  have hdne2 : d ≠ o.m - 1 := by
    intro h
    have hb' : b = (cycSucc^[o.m - 1] : Fin o.m → Fin o.m) a := by rw [← hdab, h]
    have heq : (cycSucc^[o.m - 1] : Fin o.m → Fin o.m) a = o.prev a := rfl
    exact hb2 (hb'.trans heq)
  have hle2 : 2 ≤ d := by omega
  have hleM : d ≤ o.m - 2 := by omega
  have hCcard : C.card = o.m := card_eq_cyclicOrder o.f o.hinj o.hmem
  -- the vertices of the two sub-cycles are all different
  have hfwd : ∀ t : ℕ, t ≤ d - 1 → o.f ((cycSucc^[t] : Fin o.m → Fin o.m) a) ≠ o.f b := by
    intro t ht he
    have htm : t < o.m := (lt_of_le_succ_sub_one (d := d) hle2 ht).trans hdm
    have hne : t ≠ d := ne_of_le_succ_sub_one hle2 ht
    have heq : (cycSucc^[t] : Fin o.m → Fin o.m) a = (cycSucc^[d] : Fin o.m → Fin o.m) a :=
      o.hinj (he.trans (congrArg o.f hdab).symm)
    exact cycSucc_pow_inj a (p := t) (q := d) htm hdm hne heq
  have hbwd : ∀ t : ℕ, t ≤ o.m - 1 - d → o.f ((cycSucc^[t] : Fin o.m → Fin o.m) b) ≠ o.f a := by
    intro t ht he
    have htm : t < o.m := lt_of_le_sub_succ (m := o.m) (d := d) hd0 hdm ht
    have hq : o.m - d < o.m := sub_lt_self_of_pos hd0 hdm
    have hne : t ≠ o.m - d := by
      have h1 : t + 1 + d ≤ o.m := by omega
      exact ne_of_le_sub_succ' h1
    have hba : ((cycSucc^[t] : Fin o.m → Fin o.m) b) = a := o.hinj he
    have heq : (cycSucc^[t] : Fin o.m → Fin o.m) b
        = (cycSucc^[o.m - d] : Fin o.m → Fin o.m) b := hba.trans (arc_rev hdm hdab).symm
    exact cycSucc_pow_inj b (p := t) (q := o.m - d) htm hq hne heq
  by_cases hdeven : d % 2 = 0
  · -- the forward sub-cycle is odd, of `d + 1 ≤ m - 1` vertices
    have hD : IsOddCycle G ((Finset.univ : Finset (Fin (d - 1 + 2))).image
        (arcFun o.m (d - 1) o.f a (o.f b))) := by
      -- the last arc vertex is adjacent to the closing vertex along the cycle itself
      have hcycnext : cycSucc ((cycSucc^[d - 1] : Fin o.m → Fin o.m) a) = b := by
        rw [← cycSucc_succ_pow o.m a (d - 1), sub_succ_self hle2, hdab]
      have hlast : G.Adj (o.f ((cycSucc^[d - 1] : Fin o.m → Fin o.m) a)) (o.f b) := by
        have h := o.hcyc ((cycSucc^[d - 1] : Fin o.m → Fin o.m) a)
        rw [hcycnext] at h
        exact h
      have hD0 := arc_isOddCycle_of_notMem (m := o.m) (d := d - 1) hm o.hm3 o.f o.hinj o.hcyc
        (sub_lt_of_two_le hle2 hdm) (sub_pos_of_two_le hle2)
        (fun t ht => hfwd t (by omega)) hadj.symm
      exact hD0 hlast (by omega)
    have hle := hshort _ hD
    have hcard : ((Finset.univ : Finset (Fin (d - 1 + 2))).image
        (arcFun o.m (d - 1) o.f a (o.f b))).card = d - 1 + 2 :=
      arc_card_of_notMem (sub_lt_of_two_le hle2 hdm) o.f o.hinj a (o.f b)
        (fun t ht => hfwd t (by omega))
    rw [hcard, hCcard] at hle
    exact absurd_of_le_sub_succ_two hle2 hleM hle
  · -- the backward sub-cycle is odd, of `m - d + 1 ≤ m - 1` vertices
    have hD : IsOddCycle G ((Finset.univ : Finset (Fin (o.m - 1 - d + 2))).image
        (arcFun o.m (o.m - 1 - d) o.f b (o.f a))) := by
      have hodd : (o.m - 1 - d) % 2 = 1 := by
        have htwo := Nat.mod_two_eq_zero_or_one d
        omega
      have hcycnext : cycSucc ((cycSucc^[o.m - 1 - d] : Fin o.m → Fin o.m) b) = a := by
        rw [← cycSucc_succ_pow o.m b (o.m - 1 - d), sub_succ_eq_sub hdm hle2, arc_rev hdm hdab]
      have hlast : G.Adj (o.f ((cycSucc^[o.m - 1 - d] : Fin o.m → Fin o.m) b)) (o.f a) := by
        have h := o.hcyc ((cycSucc^[o.m - 1 - d] : Fin o.m → Fin o.m) b)
        rw [hcycnext] at h
        exact h
      have hD0 := arc_isOddCycle_of_notMem (m := o.m) (d := o.m - 1 - d) hm o.hm3 o.f o.hinj
        o.hcyc (sub_sub_lt_of_two_le hle2 hleM) (sub_sub_pos_of_two_le hle2 hleM)
        (fun t ht => hbwd t (by omega)) hadj
      exact hD0 hlast hodd
    have hle := hshort _ hD
    have hcard : ((Finset.univ : Finset (Fin (o.m - 1 - d + 2))).image
        (arcFun o.m (o.m - 1 - d) o.f b (o.f a))).card = o.m - 1 - d + 2 :=
      arc_card_of_notMem (sub_sub_lt_of_two_le hle2 hleM) o.f o.hinj b (o.f a)
        (fun t ht => hbwd t (by omega))
    rw [hcard, hCcard] at hle
    exact absurd_of_le_sub_two hle2 hleM hle

/-- **Consecutive vertices of a shortest odd cycle are adjacent in the subgraph it induces.** -/
theorem adj_induce_cycle {C : Finset V} (o : CycleOrder G C) {a b : Fin o.m} (h : a = cycSucc b) :
    (induceFinset G C).Adj (o.f a) (o.f b) := by
  rw [induce_adj]
  refine ⟨(o.hmem (o.f a)).mpr ⟨a, rfl⟩, (o.hmem (o.f b)).mpr ⟨b, rfl⟩, ?_⟩
  have hh := (o.hcyc b).symm
  rw [← congrArg o.f h] at hh
  exact hh

/-- **The subgraph induced by a shortest odd cycle is exactly that cycle**: two of its vertices are
adjacent in `G` if and only if they are consecutive around the cycle.  So the shortest odd cycle of
`G` carries no edge other than its own. -/
theorem induceFinset_adj_of_shortest {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (o : CycleOrder G C)
    {a b : Fin o.m} (hab : a ≠ b) :
    (induceFinset G C).Adj (o.f a) (o.f b) ↔ a = cycSucc b ∨ b = cycSucc a := by
  constructor
  · intro hadj
    by_cases h1 : a = cycSucc b
    · exact Or.inl h1
    by_cases h2 : b = cycSucc a
    · exact Or.inr h2
    have hb2 : b ≠ o.prev a := by
      intro hb
      have h' : cycSucc b = cycSucc (o.prev a) := by rw [hb]
      rw [o.succ_prev] at h'
      exact h1 h'.symm
    exact False.elim ((no_chord_of_shortest_oddCycle hC hshort o (cycleOrder_odd hC o) hab h2 hb2)
      (induce_adj.mp hadj).2.2)
  · intro h
    rw [induce_adj]
    refine ⟨(o.hmem (o.f a)).mpr ⟨a, rfl⟩, (o.hmem (o.f b)).mpr ⟨b, rfl⟩, ?_⟩
    rcases h with h1 | h2
    · exact (induce_adj.mp (adj_induce_cycle o h1)).2.2
    · rw [h2]
      exact o.hcyc a

/-- **A shortest odd cycle exists whenever `G` has an odd cycle.** -/
theorem exists_shortest_oddCycle (hodd : ∃ C : Finset V, IsOddCycle G C) :
    ∃ C : Finset V, IsOddCycle G C ∧ (∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) := by
  classical
  obtain ⟨D, hD⟩ := hodd
  have hne : ((Finset.univ : Finset (Finset V)).filter (IsOddCycle G)).Nonempty := by
    refine Finset.filter_nonempty_iff.mpr ⟨D, Finset.mem_univ _, hD⟩
  obtain ⟨C, hCs, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset V)).filter (IsOddCycle G)) Finset.card hne
  have hCs' := hCs
  rw [Finset.mem_filter] at hCs'
  refine ⟨C, hCs'.2, fun D hD' => ?_⟩
  have hmem : D ∈ (Finset.univ : Finset (Finset V)).filter (IsOddCycle G) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hD'⟩
  exact hmin D hmem

/-- **A shortest odd cycle is an induced odd cycle**: two of its vertices are adjacent in `G` only
if they are consecutive around the cycle, i.e. the graph it carries on `V(C)` is the cycle itself.
Together with `JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` (a vertex outside a shortest
odd cycle of length `≥ 5` meets it in at most two vertices, two steps apart) this is the complete
local structure of `G` at a shortest odd cycle. -/
theorem isInduced_shortest_oddCycle {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (o : CycleOrder G C)
    {a b : Fin o.m} (hab : a ≠ b) :
    (induceFinset G C).Adj (o.f a) (o.f b) → a = cycSucc b ∨ b = cycSucc a :=
  (induceFinset_adj_of_shortest hC hshort o hab).mp

end

end JSP90
