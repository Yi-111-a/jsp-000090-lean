/-
# JSP-000090 — the *counting* half of the 2-cut decomposition

`JSPProblem/Separator.lean` (round 42) formalised the **2-cut decomposition** of `G`: a split
`V = {a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete, i.e. `{a, b}` is a vertex cut.
It proved that a cycle of `G` avoiding the cut lies in a single part, that the odd cycle transversal
and the conclusion of Erdős #73 are additive over such a split (`erdos73On_of_split`, with the
constant `m * t + 2`), and that the Erdős–Pósa hypothesis restricts to the pieces.

That file named two gaps, and both are the *counting* half of the same decomposition:

1. a cycle of `G` meeting **exactly one** vertex of the cut was not shown to lie in a piece — this
   is what forces the decomposition to charge **both** vertices `a` and `b` of the cut;
2. the packing half was only proved in the easy direction (the bound restricts to the pieces); the
   full decomposition `card 𝒟 ≤ 2 + t * r` — bounding the packing number of `G` *from* the packing
   numbers of the parts — was missing.

This file closes both gaps, and with them produces a **strictly stronger instance of the headline
theorem** than round 42's:

* **`VertexSplit.cycle_subset_piece_of_not_mem`** — **a cycle which contains `a` but not `b` lies in
  a single half-piece `T_i ∪ {a}`** (and symmetrically for `b`).  This is the companion of
  `VertexSplit.cycle_subset_parts` that round 42 named; the proof walks around the cycle starting at
  the vertex *after* `a`, using the cyclic order of `JSPProblem/Branch.lean`.
* **`VertexSplit.oddCycle_half_or_both`** — consequently every odd cycle of `G` is contained in a
  *half-piece* `T_i ∪ {a}` or `T_i ∪ {b}`, or contains **both** vertices of the cut.  The cycles
  using both vertices of the cut are the only "global" odd cycles of `G`.
* **`VertexSplit.card_filter_notBipartite_parts_le`** — **the counting lemma**: under Erdős's local
  hypothesis `LocIndep k G`, at most `k` of the `t` parts of a split are non-bipartite, because a
  non-bipartite part contains an odd cycle and the parts are pairwise disjoint.  So the number of
  pieces which cost anything is bounded by the **packing number**, *not* by the number of parts.
* **`erdos73On_of_split_of_bounded_pieces`** — **a new instance of the headline theorem, strictly
  stronger than round 42's `erdos73On_of_split`**: if `LocIndep k` forces `CloseToBipartite m` in
  every piece `T_i ∪ {a,b}`, then it forces `CloseToBipartite (2 + m * k) G`.  The constant no longer
  depends on the number `t` of pieces, and no bound on the odd girth is needed.
* **`erdos73On_of_split_of_bounded_branch_packing`** — the same improvement applied to round 42's
  composition with the branch-vertex instance: `2 + (m + k) * k` instead of `2 + (m + k) * t`.
* **`packing_le_of_split_decomposition`** — **the full packing decomposition**: if every packing of
  odd cycles of every part `T_i` has at most `r` members, then every packing of odd cycles of `G` has
  at most `2 + t * r` members.  This is the direction an Erdős–Pósa induction along a 2-cut needs,
  and it closes the second gap named by round 42.

What this does *not* give: it does not bound the *number of 2-cuts* of `G`, which is the remaining
structural content of Reed–Robertson–Seymour–Thomas.  See `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.Separator
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqCount : DecidableEq V := Classical.decEq V

/-! ### Swapping the two vertices of a cut -/

section Swap

variable {a b : V} {t : ℕ}

/-- **A 2-cut split of `G` at `a, b` is a 2-cut split at `b, a`**: the parts are the same. -/
def VertexSplit.swap (sp : VertexSplit G a b t) : VertexSplit G b a t where
  parts := sp.parts
  hne := sp.hne
  hdisj := sp.hdisj
  hcov := by
    intro x
    rcases sp.hcov x with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  hanti := sp.hanti
  hnadj := fun h => sp.hnadj h.symm

end Swap

/-! ### A cycle meeting exactly one vertex of the cut lies in a half-piece -/

section HalfPiece

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **A cycle which contains `a` but not `b` lies in a single half-piece `T_i ∪ {a}`.**

This is the companion of `VertexSplit.cycle_subset_parts` that round 42 named as missing: the
vertices of the cycle other than `a` are walked around starting at the vertex which follows `a`, and
consecutive vertices of the walk are adjacent and avoid the cut, so `VertexSplit.mem_part_of_adj`
keeps them all in one part.

The walk is indexed by the *cyclic order* of the cycle (`JSPProblem/Branch.lean`): starting at
`cycSucc j₀`, the vertex `a` sits `m - 1` steps back, so the first `m - 1` steps of the walk visit
every vertex of the cycle except `a`, exactly once. -/
theorem VertexSplit.cycle_subset_piece_of_not_mem {C : Finset V} (hC : IsOddCycle G C)
    (ha : a ∈ C) (hb : b ∉ C) : ∃ i : Fin t, C ⊆ insert a (sp.parts i) := by
  classical
  obtain ⟨o, _⟩ := hC.cycleOrder
  obtain ⟨j₀, hj₀⟩ := (o.hmem a).mp ha
  have hm3 : (0 : ℕ) < o.m := by omega
  have hle : o.m - 1 ≤ o.m := by
    calc o.m - 1 ≤ (o.m - 1) + 1 := Nat.le_add_right (o.m - 1) 1
      _ = o.m := Nat.sub_add_cancel hm3
  have hsub : o.m - 1 < o.m := by
    calc o.m - 1 < (o.m - 1) + 1 := Nat.lt_add_one _
      _ = o.m := Nat.sub_add_cancel hm3
  have hlt1 : (0 : ℕ) < o.m - 1 := Nat.sub_pos_of_lt (by have := o.hm3; omega)
  -- the index of `a` is `m - 1` steps back from the index of the vertex which follows it
  have hback : ((cycSucc^[o.m - 1] : Fin o.m → Fin o.m) (cycSucc j₀)) = j₀ := by
    simpa [CycleOrder.prev] using o.prev_succ j₀
  have hstep : ∀ t : ℕ, G.Adj (o.f ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀)))
      (o.f ((cycSucc^[t + 1] : Fin o.m → Fin o.m) (cycSucc j₀))) := by
    intro t
    have h := o.hcyc ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀))
    rw [← o.iter_succ (cycSucc j₀) t] at h
    exact h
  have hmemC : ∀ t : ℕ, o.f ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀)) ∈ C := by
    intro t
    exact (o.hmem _).mpr ⟨(cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀), rfl⟩
  have hneA : ∀ t : ℕ, t < o.m - 1 →
      o.f ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀)) ≠ a := by
    intro t ht hcon
    have hidx : ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀)) = j₀ :=
      o.hinj (hcon.trans hj₀.symm)
    rcases Nat.lt_or_ge t 1 with h | h
    · have h0 : (0 : ℕ) = t := by omega
      have hcon0 : o.f (cycSucc j₀) = a := by
        rw [← h0] at hcon
        exact hcon
      exact o.step_ne j₀ (hcon0.symm ▸ hj₀)
    · have hidx' : ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀))
          = ((cycSucc^[o.m - 1] : Fin o.m → Fin o.m) (cycSucc j₀)) := by
        calc cycSucc^[t] (cycSucc j₀) = j₀ := hidx
          _ = cycSucc^[o.m - 1] (cycSucc j₀) := hback.symm
      exact absurd hidx' (cycSucc_pow_inj (m := o.m) (cycSucc j₀) (p := t) (q := o.m - 1)
        (Nat.lt_of_lt_of_le ht hle) hsub (Nat.ne_of_lt ht))
  have hneB : ∀ t : ℕ, t < o.m - 1 →
      o.f ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀)) ≠ b := by
    intro t ht hcon
    exact hb (hcon ▸ hmemC t)
  obtain ⟨i₀, hi₀⟩ := sp.mem_parts_of_not_mem_cut (o.f ((cycSucc^[0] : Fin o.m → Fin o.m) (cycSucc j₀)))
    (hneA 0 hlt1) (hneB 0 hlt1)
  have hmem_all : ∀ t : ℕ, t < o.m - 1 →
      o.f ((cycSucc^[t] : Fin o.m → Fin o.m) (cycSucc j₀)) ∈ sp.parts i₀ := by
    intro t ht
    induction t with
    | zero => exact hi₀
    | succ t ih =>
        have hprev : t < o.m - 1 := by omega
        exact sp.mem_part_of_adj (hstep t) (ih hprev) (hneA t hprev) (hneB t hprev)
          (hneA (t + 1) (by omega)) (hneB (t + 1) (by omega))
  refine ⟨i₀, fun x hx => ?_⟩
  by_cases hxa : x = a
  · exact Finset.mem_insert.mpr (Or.inl hxa)
  obtain ⟨j, hj⟩ := (o.hmem x).mp hx
  have hjne : j ≠ j₀ := by
    intro hcon
    rw [hcon] at hj
    exact hxa (hj ▸ hj₀)
  obtain ⟨t, ht, heq⟩ := o.exists_iter (cycSucc j₀) j
  have htm : t < o.m - 1 := by
    by_contra hcon
    have h2' : t = o.m - 1 := by omega
    have heq' : ((cycSucc^[o.m - 1] : Fin o.m → Fin o.m) (cycSucc j₀)) = j := by
      rw [h2'] at heq
      exact heq
    exact hjne (heq'.symm.trans hback)
  rw [← hj, ← heq]
  exact Finset.mem_insert.mpr (Or.inr (hmem_all t htm))

/-- **A cycle which contains `b` but not `a` lies in a single half-piece `T_i ∪ {b}`.**

The parts of `sp.swap` are those of `sp`, so the half-piece obtained is a part of `sp` together
with `b`. -/
theorem VertexSplit.cycle_subset_piece_of_not_mem' {C : Finset V} (hC : IsOddCycle G C)
    (ha : a ∉ C) (hb : b ∈ C) : ∃ i : Fin t, C ⊆ insert b (sp.parts i) := by
  obtain ⟨i, hi⟩ := sp.swap.cycle_subset_piece_of_not_mem hC hb ha
  refine ⟨i, fun x hx => ?_⟩
  rcases Finset.mem_insert.mp (hi hx) with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr h)

/-- **Every odd cycle of `G` is contained in a half-piece `T_i ∪ {a}` or `T_i ∪ {b}`, or contains
both vertices of the cut.**

Together with `VertexSplit.cycle_subset_parts` this is the **complete local structure at a 2-cut**:
an odd cycle of `G` is either local to one part, local to one half-piece (it uses one vertex of the
cut), or it uses *both* vertices of the cut.  In particular the decomposition of round 42
(`oddCycle_piece_or_avoid`) is not optimal: only cycles using both `a` and `b` are "global". -/
theorem VertexSplit.oddCycle_half_or_both {C : Finset V} (hC : IsOddCycle G C) :
    (∃ i : Fin t, C ⊆ insert a (sp.parts i)) ∨ (∃ i : Fin t, C ⊆ insert b (sp.parts i)) ∨
      (a ∈ C ∧ b ∈ C) := by
  by_cases haa : a ∈ C
  · by_cases hbb : b ∈ C
    · exact Or.inr (Or.inr ⟨haa, hbb⟩)
    · obtain ⟨i, hi⟩ := sp.cycle_subset_piece_of_not_mem hC haa hbb
      exact Or.inl ⟨i, hi⟩
  · by_cases hbb : b ∈ C
    · obtain ⟨i, hi⟩ := sp.cycle_subset_piece_of_not_mem' hC haa hbb
      exact Or.inr (Or.inl ⟨i, hi⟩)
    · have hcut : C ∩ ({a, b} : Finset V) = ∅ := (Finset.disjoint_iff_inter_eq_empty).mp
        (Finset.disjoint_left.mpr (by
          intro x hxC hxab
          rcases Finset.mem_insert.mp hxab with h | h
          · exact absurd (h ▸ hxC) haa
          · exact absurd (Finset.mem_singleton.mp h ▸ hxC) hbb))
      obtain ⟨i, hi⟩ := sp.cycle_subset_parts hC hcut
      exact Or.inl ⟨i, fun x hx => Finset.mem_insert.mpr (Or.inr (hi hx))⟩

end HalfPiece

/-! ### Counting: only the non-bipartite parts cost anything -/

section Count

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **A bipartite induced subgraph of a bipartite induced subgraph is bipartite**: the 2-colouring
of the larger one restricts. -/
theorem IsBipartite.induceFinset_subset {s u : Finset V} [Fintype V]
    (h : (induceFinset G s).IsBipartite) (hsu : u ⊆ s) :
    (induceFinset G u).IsBipartite := by
  obtain ⟨c, hc⟩ := h
  refine ⟨SimpleGraph.Coloring.mk c fun hadj => ?_⟩
  exact hc (induce_adj.mpr ⟨hsu hadj.1, hsu hadj.2.1, hadj.2.2⟩)

local instance instDecidableNonBipartite (sp : VertexSplit G a b t) :
    DecidablePred (fun i : Fin t => ¬ (induceFinset G (sp.parts i)).IsBipartite) :=
  fun _ => Classical.propDecidable _

/-- **The non-bipartite parts of a split**: the parts `T_i` whose induced subgraph is not bipartite.

A bipartite part has an empty odd cycle transversal, so these are exactly the parts which cost
something in the decomposition of round 42 — and, by `VertexSplit.card_nonBipartiteParts_le` below,
there are at most `k` of them when `LocIndep k G` holds. -/
def VertexSplit.nonBipartiteParts (sp : VertexSplit G a b t) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter (fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite)

theorem VertexSplit.mem_nonBipartiteParts {i : Fin t} :
    i ∈ sp.nonBipartiteParts ↔ ¬ (induceFinset G (sp.parts i)).IsBipartite := by
  simp only [VertexSplit.nonBipartiteParts, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Every vertex of an odd cycle of the induced subgraph `G[s]` lies in `s`.**  This is the
membership half of `IsOddCycle.induceFinset` (round 40) and is what lets an odd cycle of a piece be
charged to a part. -/
theorem oddCycle_subset_induceFinset {C s : Finset V} [Fintype V]
    (hC : IsOddCycle (induceFinset G s) C) : C ⊆ s := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  intro x hx
  obtain ⟨j, hj⟩ := hCmem x |>.mp hx
  rw [← hj]
  exact (hcyc j).1

/-- **A non-bipartite part of a split contains an odd cycle, which lies in the part** (so it avoids
both vertices of the cut). -/
theorem VertexSplit.exists_oddCycle_of_mem_nonBipartiteParts {i : Fin t} [Fintype V]
    (hi : i ∈ sp.nonBipartiteParts) :
    ∃ C : Finset V, IsOddCycle G C ∧ C ⊆ sp.parts i := by
  have hnb : ¬ (induceFinset G (sp.piece i)).IsBipartite ∧
      ¬ (induceFinset G (sp.parts i)).IsBipartite :=
    ⟨fun h => sp.mem_nonBipartiteParts.mp hi (IsBipartite.induceFinset_subset h
        (fun x hx => (sp.mem_piece i x).mpr (Or.inr (Or.inr hx)))),
      sp.mem_nonBipartiteParts.mp hi⟩
  obtain ⟨C, hC⟩ : ∃ C : Finset V, IsOddCycle (induceFinset G (sp.parts i)) C := by
    by_contra hno
    exact hnb.2 (isBipartite_of_no_oddCycle (G := induceFinset G (sp.parts i)) hno)
  exact ⟨C, hC.of_induceFinset, oddCycle_subset_induceFinset hC⟩

/-- **The counting lemma of the 2-cut decomposition: under `LocIndep k G`, at most `k` of the `t`
parts of a split are non-bipartite.**

This is the key improvement over round 42, whose constant `m * t + 2` charges a transversal for
*every* piece.  Here only the non-bipartite pieces are charged, and those lie in pairwise disjoint
parts and each carries an odd cycle, so they form a packing of odd cycles of `G` — of which Erdős's
local hypothesis admits at most `k`.  The number of parts `t` is irrelevant. -/
theorem VertexSplit.card_nonBipartiteParts_le {k : ℕ} [Fintype V] (hk : LocIndep k G) :
    sp.nonBipartiteParts.card ≤ k := by
  classical
  set J := sp.nonBipartiteParts with hJ
  obtain ⟨g, hg⟩ : ∃ g : {i : Fin t // i ∈ J} → Finset V,
      ∀ i : {i : Fin t // i ∈ J}, IsOddCycle G (g i) ∧ (g i) ⊆ sp.parts i := by
    have hex : ∀ i : {i : Fin t // i ∈ J}, ∃ C : Finset V, IsOddCycle G C ∧ C ⊆ sp.parts i :=
      fun i => sp.exists_oddCycle_of_mem_nonBipartiteParts i.property
    exact ⟨fun i => Classical.choose (hex i), fun i => Classical.choose_spec (hex i)⟩
  have hne : ∀ i : {i : Fin t // i ∈ J}, (g i).Nonempty := fun i => (hg i).1.nonempty
  have hinj : Set.InjOn g ↑J.attach := by
    intro i _ j _ h
    refine Subtype.ext ?_
    by_contra hne'
    have hmem : g i ∩ g j ≠ ∅ := by
      rw [Finset.inter_eq_left.mpr fun x hx => h ▸ hx]
      exact (hne i).ne_empty
    have hmem' : g i ∩ g j = ∅ := (Finset.disjoint_iff_inter_eq_empty).mp
      (Finset.disjoint_left.mpr fun x hx hx' => by
        have h2 : x ∈ (sp.parts i.1) ∩ (sp.parts j.1) :=
          Finset.mem_inter.mpr ⟨(hg i).2 hx, (hg j).2 hx'⟩
        rw [sp.hdisj i.1 j.1 hne'] at h2
        simp at h2)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hmem
    rw [hmem'] at hx
    simp at hx
  set 𝒟 : Finset (Finset V) := J.attach.image g with h𝒟
  have hfam : IsOddCycleFamily (G := G) 𝒟 := by
    refine ⟨?_, ?_⟩
    · intro D hD E hE hDE
      obtain ⟨i, _, hiD⟩ := Finset.mem_image.mp hD
      obtain ⟨j, _, hjE⟩ := Finset.mem_image.mp hE
      by_cases hij : i = j
      · have hDE' : D = E := by rw [← hiD, ← hjE, hij]
        exact absurd hDE' hDE
      · have hmem : Disjoint (g i) (g j) := by
          refine Finset.disjoint_left.mpr fun x hx hx' => ?_
          have h2 : x ∈ (sp.parts i.1) ∩ (sp.parts j.1) :=
            Finset.mem_inter.mpr ⟨(hg i).2 hx, (hg j).2 hx'⟩
          rw [sp.hdisj i.1 j.1 (fun h => hij (Subtype.ext h))] at h2
          simp at h2
        rw [hiD, hjE] at hmem
        exact Finset.disjoint_iff_inter_eq_empty.mp hmem
    · intro D hD
      obtain ⟨i, _, hiD⟩ := Finset.mem_image.mp hD
      rw [← hiD]
      exact (hg i).1
  have hcard : 𝒟.card = J.card := by
    rw [h𝒟, Finset.card_image_of_injOn hinj]
    exact Finset.card_attach
  have hle : 𝒟.card ≤ k := hk.oddCycleFamily_card_le hfam
  omega

/-- **A transversal built from the non-bipartite pieces only.**  If every piece which is not
bipartite has an odd cycle transversal of at most `m` vertices, then `G` has an odd cycle
transversal of at most `2 + ∑ i ∈ J, m` vertices, where `J` is the set of non-bipartite *parts*.
Bipartite pieces contribute nothing — an odd cycle lying in a piece whose *part* is bipartite must
use one of the two vertices of the cut, and those are charged anyway.  This is the saving over
round 42, which pays a transversal for every one of the `t` pieces. -/
theorem VertexSplit.exists_transversal_nonBipartite {m : ℕ} [Fintype V]
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (sp.piece i))) :
    ∃ Y : Finset V, HitsOddCycles G Y ∧ Y.card ≤ 2 + ∑ i ∈ sp.nonBipartiteParts, m := by
  classical
  have hex : ∀ i ∈ sp.nonBipartiteParts, ∃ Z : Finset V, Z.card ≤ m ∧
      (deleteFinset (induceFinset G (sp.piece i)) Z).IsBipartite := by
    intro _i hi
    exact hpiece _i hi
  set X : Fin t → Finset V := fun i =>
    if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅ with hX
  have hXc : ∀ i : Fin t, X i =
      (if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅) := fun i => hX ▸ rfl
  have hXcard : ∀ i ∈ sp.nonBipartiteParts, (X i).card ≤ m := by
    intro i hi
    rw [hXc i, dite_eq_left hi]
    exact ((hex i hi).choose_spec).1
  have hXhits : ∀ i ∈ sp.nonBipartiteParts,
      HitsOddCycles (induceFinset G (sp.piece i)) (X i) := by
    intro i hi
    rw [hXc i, dite_eq_left hi]
    exact hitsOddCycles_of_isBipartite_delete ((hex i hi).choose_spec).2
  have hY : HitsOddCycles G (sp.cutSet X) := by
    intro C hC hdis
    by_cases hcut : C ∩ ({a, b} : Finset V) = ∅
    · obtain ⟨i, hi⟩ := sp.cycle_subset_parts hC hcut
      have hCj : IsOddCycle (induceFinset G (sp.parts i)) C := hC.induceFinset hi
      by_cases hmem : i ∈ sp.nonBipartiteParts
      · have hCpiece : IsOddCycle (induceFinset G (sp.piece i)) C := hC.induceFinset
            (Finset.Subset.trans hi
              (Finset.Subset.trans (Finset.subset_insert b _) (Finset.subset_insert a _)))
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hXhits i hmem C hCpiece)
        have hx1 : x ∈ C := (Finset.mem_inter.mp hx).1
        have hx2 : x ∈ X i := (Finset.mem_inter.mp hx).2
        have hmem2 : x ∈ C ∩ sp.cutSet X := Finset.mem_inter.mpr
          ⟨hx1, (sp.mem_cutSet X x).mpr (Or.inr (Or.inr ⟨i, hx2⟩))⟩
        have hnmem : x ∉ C ∩ sp.cutSet X := by rw [hdis]; simp
        exact hnmem hmem2
      · have hb : (induceFinset G (sp.parts i)).IsBipartite := by
          by_contra hnb
          exact hmem (sp.mem_nonBipartiteParts.mpr hnb)
        exact not_isOddCycle_of_isBipartite hb ⟨C, hCj⟩
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hcut
      have hx1 : x ∈ C := (Finset.mem_inter.mp hx).1
      have hxab : x = a ∨ x = b := by
        rcases Finset.mem_insert.mp ((Finset.mem_inter.mp hx).2) with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      have hmem2 : x ∈ C ∩ sp.cutSet X := Finset.mem_inter.mpr ⟨hx1,
        (sp.mem_cutSet X x).mpr (by
          rcases hxab with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h))⟩
      have hnmem : x ∉ C ∩ sp.cutSet X := by rw [hdis]; simp
      exact hnmem hmem2
  have hcard : (sp.cutSet X).card ≤ 2 + (Finset.biUnion Finset.univ X).card := by
    unfold cutSet
    have ha : (insert a (insert b (Finset.biUnion Finset.univ X)) : Finset V).card
        ≤ (insert b (Finset.biUnion Finset.univ X) : Finset V).card + 1 :=
      Finset.card_insert_le a _
    have hb : (insert b (Finset.biUnion Finset.univ X) : Finset V).card
        ≤ (Finset.biUnion Finset.univ X).card + 1 := Finset.card_insert_le b _
    omega
  have hEq : (Finset.univ : Finset (Fin t)).biUnion X
      = sp.nonBipartiteParts.biUnion X := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      by_cases hij : i ∈ sp.nonBipartiteParts
      · exact ⟨i, hij, hx⟩
      · rw [hXc i, dite_eq_right hij] at hx
        simp at hx
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, Finset.mem_univ _, hx⟩
  have hcard' : (Finset.biUnion Finset.univ X).card ≤ ∑ i ∈ sp.nonBipartiteParts, m := by
    rw [hEq]
    calc (sp.nonBipartiteParts.biUnion X).card ≤ ∑ i ∈ sp.nonBipartiteParts, (X i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ sp.nonBipartiteParts, m := Finset.sum_le_sum fun i hi => hXcard i hi
  have : 2 + (Finset.biUnion Finset.univ X).card ≤ 2 + ∑ i ∈ sp.nonBipartiteParts, m :=
    Nat.add_le_add_left hcard' 2
  exact ⟨sp.cutSet X, hY, hcard.trans this⟩

/-- **The 2-cut decomposition with the counting bound.**  If every piece of a 2-cut which is not
bipartite is `CloseToBipartite m`, and `G` satisfies `LocIndep k`, then `G` is
`CloseToBipartite (2 + m * k)`: only the non-bipartite pieces are charged and there are at most
`k` of them. -/
theorem closeToBipartite_of_split_of_bounded_pieces (k m t : ℕ) [Fintype V]
    (sp : VertexSplit G a b t)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts, CloseToBipartite m (induceFinset G (sp.piece i)))
    (hG : LocIndep k G) : CloseToBipartite (2 + m * k) G := by
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_nonBipartite (m := m) hpiece
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ k := sp.card_nonBipartiteParts_le hG
  have hsum : (∑ i ∈ sp.nonBipartiteParts, m) ≤ m * k := by
    have h1 : (∑ _i ∈ sp.nonBipartiteParts, m)
        = (sp.nonBipartiteParts : Finset (Fin t)).card * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h2 : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ m * k := by
      have h2' : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ k * m :=
        Nat.mul_le_mul hJ (le_refl m)
      rwa [Nat.mul_comm k m] at h2'
    omega
  have hcard : Y.card ≤ 2 + m * k :=
    hYcard.trans (Nat.add_le_add_left hsum 2)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2 + m * k)).mpr ⟨Y, hcard, hY⟩

/-- **A new instance of the headline theorem, strictly stronger than round 42's
`erdos73On_of_split`**: if `LocIndep k` forces `CloseToBipartite m` in every piece
`T_i ∪ {a, b}` of a 2-cut, then it forces `CloseToBipartite (2 + m * k) G`.

The constant `2 + m * k` no longer depends on the number `t` of pieces of the cut: only the
non-bipartite ones are charged, and there are at most `k` of them
(`VertexSplit.card_nonBipartiteParts_le`).  No bound on the odd girth is used. -/
theorem erdos73On_of_split_of_bounded_pieces (k m t : ℕ) [Fintype V] (sp : VertexSplit G a b t)
    (hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) →
      CloseToBipartite m (induceFinset G (sp.piece i)))
    (hG : LocIndep k G) : CloseToBipartite (2 + m * k) G := by
  have hLoc : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) :=
    fun i => hG.of_induceFinset (sp.piece i)
  exact closeToBipartite_of_split_of_bounded_pieces (k := k) (m := m) (t := t) sp
    (fun i _ => hpiece i (hLoc i)) hG

/-- **The same improvement applied to the composition with the branch-vertex instance of round 38:
`2 + (m + k) * k` instead of round 42's `2 + (m + k) * t`.** -/
theorem erdos73On_of_split_of_bounded_branch_packing (k m t : ℕ) [Fintype V]
    (sp : VertexSplit G a b t)
    (hB : ∀ i : Fin t, ∃ B : Finset V, B ⊆ sp.piece i ∧ B.card ≤ m ∧
      ∀ v : V, BranchVertex (induceFinset G (sp.piece i)) v → v ∈ B)
    (hG : LocIndep k G) : CloseToBipartite (2 + (m + k) * k) G := by
  have hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) →
      CloseToBipartite (m + k) (induceFinset G (sp.piece i)) := by
    intro i hLoc
    obtain ⟨B, -, hBcard, hBall⟩ := hB i
    exact erdos73On_of_few_high_degree (k := k) (m := m) V (inferInstance : Fintype V)
      (induceFinset G (sp.piece i)) hLoc B hBall hBcard
  exact erdos73On_of_split_of_bounded_pieces (k := k) (m := m + k) (t := t) sp hpiece hG

end Count

/-! ### The full packing decomposition -/

section PackingDecomp

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **A pairwise disjoint family of finsets which all contain one vertex has at most one member.** -/
theorem card_le_one_of_common {s : Finset (Finset V)} (hdis : DisjointFamily s) (x : V)
    (hall : ∀ D ∈ s, x ∈ D) : s.card ≤ 1 := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨D, hD⟩ := hs
    by_cases hsingle : ∀ E ∈ s, E = D
    · have hse : s = {D} := by
        ext E
        constructor
        · intro hE
          rw [hsingle E hE]
          exact Finset.mem_singleton_self D
        · intro hE
          have hED : E = D := Finset.mem_singleton.mp hE
          exact hED.symm ▸ hD
      rw [hse]
      simp
    · have hex : ∃ E ∈ s, E ≠ D := by
        by_contra hcon
        refine hsingle ?_
        intro E hE
        by_contra hED
        exact hcon ⟨E, hE, hED⟩
      obtain ⟨E, hE, hED⟩ := hex
      have hmem : x ∈ D ∩ E := Finset.mem_inter.mpr ⟨hall D hD, hall E hE⟩
      rw [hdis D hD E hE hED.symm] at hmem
      simp at hmem
  · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hse]
    simp

/-- **The full packing decomposition along a 2-cut.**  If every packing of odd cycles of every part
`T_i` has at most `r` members, then every packing of odd cycles of `G` has at most `2 + t * r`
members.

This is the direction round 42 named as missing.  A packing of `G` splits into the members which
meet the two vertices of the cut — at most **two** of them, since the members are pairwise
vertex-disjoint — and, for each part `T_i`, the members which avoid the cut, which form a packing of
odd cycles of the induced subgraph on `T_i` (each of them lies in a single part by
`VertexSplit.cycle_subset_parts`).  It is the half an Erdős–Pósa induction along a 2-cut
decomposition needs in order to bound the packing number of `G` from above. -/
theorem packing_le_of_split_decomposition [Fintype V] {r : ℕ}
    (hpart : ∀ i : Fin t, ∀ 𝒞 : Finset (Finset V),
      IsOddCycleFamily (G := induceFinset G (sp.parts i)) 𝒞 → 𝒞.card ≤ r)
    {𝒞 : Finset (Finset V)} (h𝒞 : IsOddCycleFamily (G := G) 𝒞) : 𝒞.card ≤ 2 + t * r := by
  classical
  -- the members which meet the cut: at most two of them
  set A : Finset (Finset V) := 𝒞.filter (fun D => ¬ Disjoint D ({a, b} : Finset V)) with hA
  set B : Finset (Finset V) := 𝒞.filter (fun D => Disjoint D ({a, b} : Finset V)) with hB
  have hAunion : A ∪ B = 𝒞 := by
    ext D
    simp only [hA, hB, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro (⟨hD, hn⟩ | ⟨hD, hd⟩)
      · exact hD
      · exact hD
    · intro hD
      by_cases hn : Disjoint D ({a, b} : Finset V)
      · exact Or.inr ⟨hD, hn⟩
      · exact Or.inl ⟨hD, hn⟩
  have hAint : A ∩ B = ∅ := by
    refine Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_left.mpr fun D hDA hDB => ?_)
    obtain ⟨-, hn⟩ := Finset.mem_filter.mp hDA
    obtain ⟨-, hd⟩ := Finset.mem_filter.mp hDB
    exact absurd hd hn
  have hsplit : A.card + B.card = 𝒞.card := by
    have h := Finset.card_union_add_card_inter A B
    rw [hAunion, hAint] at h
    simp at h
    omega
  have hdisA : DisjointFamily A :=
    fun D hD E hE hDE =>
      h𝒞.1 D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 hDE
  have hcardA : A.card ≤ 2 := by
    set Aa : Finset (Finset V) := A.filter (fun D => a ∈ D) with hAa
    set Ab : Finset (Finset V) := A.filter (fun D => b ∈ D) with hAb
    have hsub : A ⊆ Aa ∪ Ab := by
      intro D hD
      have hnn : D ∩ ({a, b} : Finset V) ≠ ∅ := fun h =>
        (Finset.mem_filter.mp hD).2 (Finset.disjoint_iff_inter_eq_empty.mpr h)
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hnn
      have hxD : x ∈ D := (Finset.mem_inter.mp hx).1
      rcases Finset.mem_insert.mp ((Finset.mem_inter.mp hx).2) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hD, h.symm ▸ hxD⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hD, (Finset.mem_singleton.mp h).symm ▸ hxD⟩)
    have hdisAa : DisjointFamily Aa :=
      fun D hD E hE hDE => hdisA D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 hDE
    have hdisAb : DisjointFamily Ab :=
      fun D hD E hE hDE => hdisA D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 hDE
    have haa : Aa.card ≤ 1 :=
      card_le_one_of_common (s := Aa) hdisAa a fun D hD => (Finset.mem_filter.mp hD).2
    have hbb : Ab.card ≤ 1 :=
      card_le_one_of_common (s := Ab) hdisAb b fun D hD => (Finset.mem_filter.mp hD).2
    calc A.card ≤ (Aa ∪ Ab).card := Finset.card_le_card hsub
      _ ≤ Aa.card + Ab.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  -- the members which avoid the cut: one packing inside each part
  set D : Fin t → Finset (Finset V) := fun i => B.filter (fun C => C ⊆ sp.parts i) with hD
  have hDi : ∀ i : Fin t, IsOddCycleFamily (G := induceFinset G (sp.parts i)) (D i) := by
    intro i
    refine ⟨?_, ?_⟩
    · intro C hC E hE hCE
      exact h𝒞.1 C (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1
        E (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1 hCE
    · intro C hC
      exact (h𝒞.2 C (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1).induceFinset
        (Finset.mem_filter.mp hC).2
  have hcov : B ⊆ (Finset.univ : Finset (Fin t)).biUnion D := by
    intro C hC
    obtain ⟨hCC, hCcut⟩ := Finset.mem_filter.mp hC
    have hcut : C ∩ ({a, b} : Finset V) = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hCcut
    obtain ⟨i, hi⟩ := sp.cycle_subset_parts (h𝒞.2 C hCC) hcut
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hC, hi⟩⟩
  have hcardB : B.card ≤ t * r := by
    have h1 : B.card ≤ ((Finset.univ : Finset (Fin t)).biUnion D).card :=
      Finset.card_le_card hcov
    have h2 : ((Finset.univ : Finset (Fin t)).biUnion D).card ≤ ∑ _i : Fin t, (r : ℕ) := by
      calc ((Finset.univ : Finset (Fin t)).biUnion D).card ≤ ∑ i : Fin t, (D i).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin t, (r : ℕ) := Finset.sum_le_sum fun i hi => hpart i (D i) (hDi i)
    have h3 : (∑ _i : Fin t, (r : ℕ)) = r * t := by
      calc (∑ _i : Fin t, (r : ℕ)) = (Finset.univ : Finset (Fin t)).card * r := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rfl
        _ = r * t := by rw [Finset.card_fin, Nat.mul_comm]
    have h4 : r * t = t * r := Nat.mul_comm r t
    omega
  omega

end PackingDecomp

/-! ### The same statements in the vocabulary of Erdős–Pósa -/

section EP

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **The counting lemma, in the vocabulary of Erdős–Pósa**: if every packing of odd cycles of `G`
has at most `p` members, then at most `p` of the `t` parts of a split are non-bipartite.  (The
proof is the one of `VertexSplit.card_nonBipartiteParts_le`, with the packing bound in place of
Erdős's local hypothesis — the two are interchangeable, `LocIndep.oddCycleFamily_card_le`.) -/
theorem VertexSplit.card_nonBipartiteParts_le_pack {p : ℕ} [Fintype V]
    (hpack : ∀ 𝒞 : Finset (Finset V), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ p) :
    sp.nonBipartiteParts.card ≤ p := by
  classical
  set J := sp.nonBipartiteParts with hJ
  obtain ⟨g, hg⟩ : ∃ g : {i : Fin t // i ∈ J} → Finset V,
      ∀ i : {i : Fin t // i ∈ J}, IsOddCycle G (g i) ∧ (g i) ⊆ sp.parts i := by
    have hex : ∀ i : {i : Fin t // i ∈ J}, ∃ C : Finset V, IsOddCycle G C ∧ C ⊆ sp.parts i :=
      fun i => sp.exists_oddCycle_of_mem_nonBipartiteParts i.property
    exact ⟨fun i => Classical.choose (hex i), fun i => Classical.choose_spec (hex i)⟩
  have hne : ∀ i : {i : Fin t // i ∈ J}, (g i).Nonempty := fun i => (hg i).1.nonempty
  have hinj : Set.InjOn g ↑J.attach := by
    intro i _ j _ h
    refine Subtype.ext ?_
    by_contra hne'
    have hinter : g i ∩ g j ≠ ∅ := by
      rw [Finset.inter_eq_left.mpr fun x hx => h ▸ hx]
      exact (hne i).ne_empty
    have hmem' : g i ∩ g j = ∅ := (Finset.disjoint_iff_inter_eq_empty).mp
      (Finset.disjoint_left.mpr fun x hx hx' => by
        have h2 : x ∈ (sp.parts i.1) ∩ (sp.parts j.1) :=
          Finset.mem_inter.mpr ⟨(hg i).2 hx, (hg j).2 hx'⟩
        rw [sp.hdisj i.1 j.1 hne'] at h2
        simp at h2)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hinter
    rw [hmem'] at hx
    simp at hx
  set 𝒟 : Finset (Finset V) := J.attach.image g with h𝒟
  have hfam : IsOddCycleFamily (G := G) 𝒟 := by
    refine ⟨?_, ?_⟩
    · intro D hD E hE hDE
      obtain ⟨i, _, hiD⟩ := Finset.mem_image.mp hD
      obtain ⟨j, _, hjE⟩ := Finset.mem_image.mp hE
      by_cases hij : i = j
      · have hDE' : D = E := by rw [← hiD, ← hjE, hij]
        exact absurd hDE' hDE
      · have hmem : Disjoint (g i) (g j) := by
          refine Finset.disjoint_left.mpr fun x hx hx' => ?_
          have h2 : x ∈ (sp.parts i.1) ∩ (sp.parts j.1) :=
            Finset.mem_inter.mpr ⟨(hg i).2 hx, (hg j).2 hx'⟩
          rw [sp.hdisj i.1 j.1 (fun h => hij (Subtype.ext h))] at h2
          simp at h2
        rw [hiD, hjE] at hmem
        exact Finset.disjoint_iff_inter_eq_empty.mp hmem
    · intro D hD
      obtain ⟨i, _, hiD⟩ := Finset.mem_image.mp hD
      rw [← hiD]
      exact (hg i).1
  have hcard : 𝒟.card = J.card := by
    rw [h𝒟, Finset.card_image_of_injOn hinj]
    exact Finset.card_attach
  have hle : 𝒟.card ≤ p := hpack 𝒟 hfam
  omega

/-- **The 2-cut decomposition with the counting bound, in the vocabulary of Erdős–Pósa.**  If every
packing of odd cycles of `G` has at most `p` members, and every non-bipartite piece of a 2-cut of
`G` is `CloseToBipartite m`, then `G` is `CloseToBipartite (2 + m * p)`.  This is the form the
induction along a 2-cut decomposition takes: no odd girth, no branch vertices, only the packing
number. -/
theorem closeToBipartite_of_split_of_bounded_pieces_pack (p m t : ℕ) [Fintype V]
    (sp : VertexSplit G a b t)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts, CloseToBipartite m (induceFinset G (sp.piece i)))
    (hpack : ∀ 𝒞 : Finset (Finset V), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ p) :
    CloseToBipartite (2 + m * p) G := by
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_nonBipartite (m := m) hpiece
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ p := sp.card_nonBipartiteParts_le_pack hpack
  have hsum : (∑ i ∈ sp.nonBipartiteParts, m) ≤ m * p := by
    have h1 : (∑ _i ∈ sp.nonBipartiteParts, m)
        = (sp.nonBipartiteParts : Finset (Fin t)).card * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h2 : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ p * m :=
      Nat.mul_le_mul hJ (le_refl m)
    have h3 : p * m = m * p := Nat.mul_comm p m
    omega
  have hcard : Y.card ≤ 2 + m * p := hYcard.trans (Nat.add_le_add_left hsum 2)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2 + m * p)).mpr ⟨Y, hcard, hY⟩

end EP

/-! ### The precise reduction to the 3-connected case -/

section Reduction

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- **`G` has a proper 2-cut**: a split of `V` into `{a, b} ⊔ T₁ ⊔ … ⊔ T_t` with `t ≥ 2` pairwise
anticomplete parts.  (The bound `t ≥ 2` is what makes the pair `{a, b}` a *vertex cut* rather than a
mere non-adjacent pair.) -/
def HasProperSplit (G : SimpleGraph V) : Prop :=
  ∃ (a b : V) (t : ℕ) (sp : VertexSplit G a b t), 2 ≤ t

/-- **`G` has no proper 2-cut**: `G` is 3-connected in the sense that matters for odd cycles. -/
def NoProperSplit (G : SimpleGraph V) : Prop := ¬ HasProperSplit G

/-- **`SplitDepth G d`**: `G` can be decomposed by at most `d` successive 2-cuts into graphs with
**no** proper 2-cut.  `d = 0` is exactly `NoProperSplit G`; at each step either `G` is already
2-cut-free, or `G` has a proper 2-cut every piece of which has depth `< d`.

This is the invariant of the classical induction along a 2-cut decomposition.  The whole difficulty
of Erdős–Pósa for odd cycles is the missing bound `∀ G, SplitDepth G d` for some `d` depending on
the packing number — the content of the Mader/Reed–Robertson–Seymour–Thomas structure theorem,
which is not in the pinned Mathlib import slice. -/
def SplitDepth (G : SimpleGraph V) : ℕ → Prop
  | 0 => NoProperSplit G
  | d + 1 => NoProperSplit G ∨ ∃ (a b : V) (t : ℕ) (sp : VertexSplit G a b t) (h2t : 2 ≤ t),
      ∀ i : Fin t, SplitDepth (induceFinset G (sp.piece i)) d

/-- **The bound obtained by decomposing `G` with `d` successive 2-cuts**, assuming the 2-cut-free
case holds with the function `m`: at each level one pays `2 + p * (bound of the level below)`, `p`
being the packing number, because at most `p` pieces are non-bipartite
(`VertexSplit.card_nonBipartiteParts_le_pack`). -/
def splitBound (m : ℕ → ℕ) (p d : ℕ) : ℕ :=
  Nat.rec (m p) (fun _ b => max (m p) (2 + p * b)) d

/-- **`splitBound m p d ≥ m p`**: the 2-cut decomposition never makes the bound smaller than the
2-cut-free bound it starts from. -/
theorem le_splitBound (m : ℕ → ℕ) (p d : ℕ) : m p ≤ splitBound m p d := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ e ih => exact Nat.le_max_left _ _

/-- **THE PRECISE REDUCTION: Erdős–Pósa for odd cycles follows from (i) the 2-cut-free case and
(ii) a uniform bound on the length of chains of 2-cuts.**

Concretely: suppose that for every packing number `p` there is a constant `m p` such that a graph
with no proper 2-cut and packing number at most `p` is `CloseToBipartite (m p)`, and that every
graph with packing number at most `p` has split depth at most `d`.  Then every graph with packing
number at most `p` is `CloseToBipartite (splitBound m p d)`.

Since `erdos73_of_erdosPosa` is proved, this says: **`jsp_000090_main` follows from the 2-cut-free
case of Erdős–Pósa together with a uniform bound on the number of 2-cuts of `G`.**  Everything
else — the local structure at a shortest odd cycle (`Chord.lean`, `Fan.lean`), the residue
induction (`Residue.lean`), the 2-cut decomposition and its counting half (`Separator.lean`,
`Count.lean`) — is proved and enters only through the two hypotheses. -/
theorem erdos73_of_noSplit2_of_bounded_splitDepth (d : ℕ) (m : ℕ → ℕ)
    (hm : ∀ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (p : ℕ),
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := H) C → C.card ≤ p) →
      NoProperSplit H → CloseToBipartite (m p) H)
    (hd : ∀ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (p : ℕ),
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := H) C → C.card ≤ p) → SplitDepth H d)
    (p : ℕ) : OddCycleErdosPosa.{u} p := by
  have key : ∀ (W : Type u) (instW : Fintype W) (H : SimpleGraph W) (p' : ℕ) (d' : ℕ),
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := H) C → C.card ≤ p') →
      SplitDepth H d' → CloseToBipartite (splitBound m p' d') H := by
    intro W instW H p' d'
    induction d' using Nat.strong_induction_on generalizing W H with
    | h d' ih =>
        intro hpack hd'
        rcases d' with _ | e
        · obtain ⟨Z, hZcard, hZbip⟩ := hm W instW H p' hpack hd'
          exact ⟨Z, hZcard, hZbip⟩
        · rcases (hd' : NoProperSplit H ∨
            ∃ (a b : W) (t : ℕ) (sp : VertexSplit H a b t) (h2t : 2 ≤ t),
              ∀ i : Fin t, SplitDepth (induceFinset H (sp.piece i)) e) with
            hfree | ⟨a, b, t, sp, h2t, hpieces⟩
          · obtain ⟨Z, hZcard, hZbip⟩ := hm W instW H p' hpack hfree
            exact ⟨Z, hZcard.trans (le_splitBound m p' (e + 1)), hZbip⟩
          · have hpi : ∀ i ∈ sp.nonBipartiteParts,
                CloseToBipartite (splitBound m p' e) (induceFinset H (sp.piece i)) := by
              intro i _
              have hpart : ∀ C : Finset (Finset W), IsOddCycleFamily
                  (G := induceFinset H (sp.piece i)) C → C.card ≤ p' := by
                intro C hC
                exact hpack C hC.of_induceFinset
              exact ih e (by omega) (W := W) (instW := instW)
                (H := induceFinset H (sp.piece i)) hpart (hpieces i)
            obtain ⟨Z, hZcard, hZbip⟩ :=
              closeToBipartite_of_split_of_bounded_pieces_pack (p := p') (m := splitBound m p' e)
                (t := t) sp hpi hpack
            have h1' : Z.card ≤ 2 + p' * splitBound m p' e :=
              hZcard.trans_eq (by rw [Nat.mul_comm p' (splitBound m p' e)])
            exact ⟨Z, h1'.trans (Nat.le_max_right _ _), hZbip⟩
  refine ⟨splitBound m p d, ?_⟩
  intro W instW H hpack
  exact key W instW H p d hpack (hd W instW H p hpack)

end Reduction

end

end JSP90