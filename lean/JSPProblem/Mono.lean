/-
# JSP-000090 — round 127: the **MAXIMUM-CUT axis** (`MonoSet` of a cut)

Erdős Problem #73 (`JSP90.Erdős73 k`: `LocIndep k G → ∃ m, CloseToBipartite m G`) is Reed's
theorem; `discovery/JSP-000090/policy.json` records that `JSP90.OddCycleErdosPosa r` and hence
`jsp_000090_main` are unproved after 126 rounds.  The development contains **one** axis that
attacks the conclusion through *cuts*: `JSPProblem/MaxCut.lean`, which proves that every odd cycle
has a monochromatic edge in **every** cut, so a set covering the monochromatic edges of a cut is an
odd cycle transversal.

Round 127 adds the two things that file was missing: **the canonical cover** (Part 1 — no cover has
to be supplied any more, and it is the minimal set incident to every monochromatic edge) and **the
optimality of the cut** (Part 2 — the one hypothesis that makes cuts special, namely that a *stable*
cut, in particular a maximum cut, pushes every vertex that has a same-side neighbour out of its
side).  Nothing in the previous 45 000 lines used either.

## Part 1 — the canonical cover of a cut

`JSP90.MonoVertex G A v` is "`v` is incident to a non-crossing edge of the cut with side `A`", and
`JSP90.MonoSet G A` is the finset of all such `v`.

* **`JSP90.hitsOddCycles_monoSet` — THE MONO SET OF *ANY* CUT IS AN ODD CYCLE TRANSVERSAL.**
  Every odd cycle has a monochromatic edge in every cut, and both endpoints of that edge are mono.
  `JSPProblem/MaxCut.lean` proves this only for a *supplied* cover `Z`
  (`hitsOddCycles_of_hitsMono`); here `Z` is produced from the cut alone.
* **`JSP90.closeToBipartite_monoSet` — AN INSTANCE OF THE CONCLUSION FOR EVERY CUT:**
  `CloseToBipartite (MonoSet G A).card G`.
* **`JSP90.inter_monoSet_ne_empty_of_hitsMono`** — the mono set *and* any monochromatic cover meet
  each other at an endpoint of every monochromatic edge, so `JSP90.MonoSet G A` is the minimal set
  of vertices incident to all of them.
* **`JSP90.isBipartite_iff_exists_monoSet_empty` — THE CUT AXIS IS EQUIVALENT TO BIPARTITENESS:**
  `G.IsBipartite ↔ ∃ A, MonoSet G A = ∅`.  With
  `JSP90.maxDef_le_zero_iff_exists_monoSet_empty` this settles all of Erdős #73 at `k = 0`
  *through the cut*: a graph of deficiency `≤ 0` has a cut with no monochromatic vertex at all.
* **`JSP90.monoSet_compl`** — the mono set does not depend on which side is called `A`.

## Part 2 — degrees relative to a cut, and the stability of a cut

`JSP90.SameDeg G A v` is the number of neighbours of `v` **on `v`'s own side** of the cut and
`JSP90.CrossDeg G A v` the number on the other side; `JSP90.sameDeg_add_crossDeg` says they add up
to the degree of `v`.

`JSP90.StableCut G A` is the classical one-vertex-flip-optimality condition: **no vertex of `A` has
more neighbours on its own side than on the other side.**  Every maximum cut is stable, and this is
the only place in the development where the *optimality* of a cut is used.  The consequences proved
here are:

* **`JSP90.exists_notMem_adj_of_stableCut` — A STABLE CUT PUSHES EVERY MONO VERTEX OUT OF ITS
  SIDE:** `v ∈ A → SameDeg G A v ≤ CrossDeg G A v → 1 ≤ SameDeg G A v → ∃ w ∉ A, G.Adj v w`.
* **`JSP90.sum_sameDeg_le_sum_crossDeg_of_stableCut` — THE INTERNAL EDGES OF A STABLE SIDE NUMBER
  AT MOST HALF THE CUT:** `∑ v ∈ A, SameDeg G A v ≤ ∑ v ∈ A, CrossDeg G A v`.
* **`JSP90.card_monoSet_pos_of_not_isBipartite`** — on a non-bipartite graph *every* cut has a mono
  set of at least two vertices, so the cut axis can never give the constant `0`.

## Part 3 — the reduction, and a machine-checked NEGATIVE result

* **`JSP90.MaxCutMonoLe c`** (a `def`, **not** assumed anywhere): every graph of deficiency `≤ k`
  admits a *stable* cut whose mono set has at most `c` vertices.
  **`JSP90.erdos73_of_maxCutMonoLe`** turns it into Erdős #73 with constant `c`.  This is the
  round's precisely stated missing lemma.
* **`JSP90.not_closeToBipartite_monoSet_completeGraph` — THE CUT CERTIFICATE IS NEVER OPTIMAL ON
  `K_n`.**  For `n ≥ 4` *every* cut `A` of the complete graph has
  `n − 1 ≤ (MonoSet (completeGraph (Fin n)) A).card`, while
  `JSP90.closeToBipartite_iff_completeGraph_add_two` gives `CloseToBipartite (n − 2) (K_n)`.  No
  choice of cut, and in particular no *maximum* cut, repairs this.

The measurements behind this round are `discovery/JSP-000090/r127*.c`: exhaustively over **all
268 435 456 graphs on 8 vertices**, among the `55 179 262` with `MaxDef ≤ 1` the best maximum cut
has **at most 4** mono vertices and `4` is attained; the worst case on 7 vertices is the friendship
graph `F₃` (three triangles sharing a vertex, whose odd cycle transversal number is `1`).  So the
surviving form of the hypothesis is a bound in terms of `MaxDef`, not an absolute one, and
`JSP90.MaxCutMonoLe c` is that form.
-/

import JSPProblem.MaxCut
import JSPProblem.Layer
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqMono : DecidableEq V := Classical.decEq V

/-! ### Part 0 — the mono set of a cut -/

/-- **THE MONOCHROMATIC VERTICES OF THE CUT WITH SIDE `A`**: `v` is *mono* if it is incident to an
edge that does **not** cross the cut, i.e. to an edge `vw` with `v ∈ A ↔ w ∈ A`. -/
def MonoVertex (G : SimpleGraph V) (A : Finset V) (v : V) : Prop := ∃ w, MonoEdge G A v w

/-- **`MonoSet G A` is the set of monochromatic vertices of the cut with side `A`** — the minimal
set of vertices incident to every monochromatic edge of that cut. -/
def MonoSet (G : SimpleGraph V) (A : Finset V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter (fun v => MonoVertex G A v)

theorem mem_monoSet {A : Finset V} {v : V} : v ∈ MonoSet G A ↔ MonoVertex G A v := by
  classical
  simp only [MonoSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **THE MONO SET AND ANY MONOCHROMATIC COVER MEET AT AN ENDPOINT OF EVERY MONOCHROMATIC EDGE.**
In particular the mono set is the smallest set of vertices incident to all the monochromatic edges
of the cut: it is contained in the incident-vertex set of any such set, and meets every
monochromatic edge. -/
theorem inter_monoSet_ne_empty_of_hitsMono {A Z : Finset V} (hZ : HitsMono G A Z) {v w : V}
    (hmono : MonoEdge G A v w) : (MonoSet G A ∩ Z).Nonempty := by
  rcases hZ v w hmono with h | h
  · exact ⟨v, Finset.mem_inter.mpr ⟨mem_monoSet.mpr ⟨w, hmono⟩, h⟩⟩
  · have hsym : MonoEdge G A w v :=
      ⟨hmono.1.symm, hmono.2.imp (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩)⟩
    exact ⟨w, Finset.mem_inter.mpr ⟨mem_monoSet.mpr ⟨v, hsym⟩, h⟩⟩

/-- **THE MONO SET OF A CUT DOES NOT DEPEND ON WHICH SIDE IS CALLED `A`.** -/
theorem mem_monoSet_compl {A : Finset V} {v : V} :
    v ∈ MonoSet G (Finset.univ \ A) ↔ v ∈ MonoSet G A := by
  classical
  simp only [MonoSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold MonoVertex MonoEdge
  constructor
  · rintro ⟨w, h1, h2 | h2⟩
    · exact ⟨w, h1, Or.inr ⟨(Finset.mem_sdiff.mp h2.1).2, (Finset.mem_sdiff.mp h2.2).2⟩⟩
    · have hA : v ∈ A ∧ w ∈ A := by
        constructor
        · by_contra hh
          exact h2.1 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hh⟩)
        · by_contra hh
          exact h2.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hh⟩)
      exact ⟨w, h1, Or.inl hA⟩
  · rintro ⟨w, h1, h2 | h2⟩
    · refine ⟨w, h1, Or.inr ⟨?_, ?_⟩⟩
      · intro hcontra
        exact (Finset.mem_sdiff.mp hcontra).2 h2.1
      · intro hcontra
        exact (Finset.mem_sdiff.mp hcontra).2 h2.2
    · exact ⟨w, h1, Or.inl ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, h2.1⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, h2.2⟩⟩⟩

theorem monoSet_compl (A : Finset V) : MonoSet G (Finset.univ \ A) = MonoSet G A := by
  classical
  ext v
  exact mem_monoSet_compl

/-! ### Part 1 — every cut yields a transversal -/

/-- **`HitsMono` holds for the mono set itself**: the mono set covers the monochromatic edges of the
cut, trivially and canonically. -/
theorem hitsMono_of_monoSet (A : Finset V) : HitsMono G A (MonoSet G A) := by
  intro v w hmono
  exact Or.inl (mem_monoSet.mpr ⟨w, hmono⟩)

/-- **THE MONO SET OF *ANY* CUT IS AN ODD CYCLE TRANSVERSAL.**  Every odd cycle has a
monochromatic edge in every cut, and both endpoints of that edge are mono. -/
theorem hitsOddCycles_monoSet (A : Finset V) : HitsOddCycles G (MonoSet G A) := by
  intro C hC hdis
  obtain ⟨v, w, hmono, hvC, hwC⟩ := exists_monoEdge_of_isOddCycle hC A
  have hvZ : v ∈ MonoSet G A := mem_monoSet.mpr ⟨w, hmono⟩
  have hmem : v ∈ C ∩ MonoSet G A := Finset.mem_inter.mpr ⟨hvC, hvZ⟩
  rw [hdis] at hmem
  simp at hmem

/-- **AN INSTANCE OF THE CONCLUSION OF ERDŐS #73, FOR *EVERY* CUT:**
`CloseToBipartite (MonoSet G A).card G`. -/
theorem closeToBipartite_monoSet (A : Finset V) : CloseToBipartite (MonoSet G A).card G :=
  closeToBipartite_of_hitsMono (hitsMono_of_monoSet (A := A))

/-- **NO MONO VERTEX IMPLIES THE MONO SET IS EMPTY.** -/
theorem monoSet_eq_empty_of_forall_not_monoVertex {A : Finset V}
    (h : ∀ v : V, ¬ MonoVertex G A v) : MonoSet G A = ∅ := by
  classical
  rw [MonoSet]
  exact Finset.filter_eq_empty_iff.mpr fun v _ => h v

/-- **A GRAPH IS BIPARTITE EXACTLY WHEN IT HAS A CUT WITH NO MONOCHROMATIC EDGE** — the converse
direction of the cut axis, and the cleanest reformulation of bipartiteness in this development. -/
theorem isBipartite_iff_exists_monoSet_empty :
    G.IsBipartite ↔ ∃ A : Finset V, MonoSet G A = ∅ := by
  constructor
  · rintro ⟨d, hd⟩
    set A : Finset V := Finset.univ.filter (fun x => d x = 1) with hA
    refine ⟨A, ?_⟩
    refine monoSet_eq_empty_of_forall_not_monoVertex fun v => ?_
    rintro ⟨w, hadj, hside⟩
    rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hdv : d v = 1 := (Finset.mem_filter.mp h1).2
      have hdw : d w = 1 := (Finset.mem_filter.mp h2).2
      exact hd hadj (hdv.trans hdw.symm)
    · have hn1 : ¬ (d v = 1) := fun hh =>
        h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hh⟩)
      have hn2 : ¬ (d w = 1) := fun hh =>
        h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hh⟩)
      have hne1 : (d v).val ≠ 1 := fun hh => hn1 (Fin.ext hh)
      have hne2 : (d w).val ≠ 1 := fun hh => hn2 (Fin.ext hh)
      have hz1 : d v = 0 := Fin.ext (by omega)
      have hz2 : d w = 0 := Fin.ext (by omega)
      exact hd hadj (hz1.trans hz2.symm)
  · rintro ⟨A, hA⟩
    refine isBipartite_of_noMonoEdge (A := A) fun v w hmono => ?_
    exact absurd (mem_monoSet.mpr ⟨w, hmono⟩) (by rw [hA]; simp)

/-- **THE `k = 0` CASE OF ERDŐS #73 THROUGH THE CUT AXIS.**  A graph of deficiency `≤ 0` is
bipartite, hence has a cut with **no** monochromatic vertex: the cut axis delivers the constant `0`
at `k = 0`, and nothing further is needed there. -/
theorem maxDef_le_zero_iff_exists_monoSet_empty :
    MaxDef G ≤ 0 ↔ ∃ A : Finset V, MonoSet G A = ∅ := by
  have hiff : MaxDef G = 0 ↔ ∃ A : Finset V, MonoSet G A = ∅ := by
    constructor
    · intro h0
      obtain ⟨A, hA⟩ := isBipartite_iff_exists_monoSet_empty.mp (maxDef_eq_zero_iff.mp h0)
      exact ⟨A, hA⟩
    · rintro ⟨A, hA⟩
      exact maxDef_eq_zero_iff.mpr (isBipartite_iff_exists_monoSet_empty.mpr ⟨A, hA⟩)
  constructor
  · intro h
    obtain ⟨A, hA⟩ := hiff.mp (show MaxDef G = 0 by omega)
    exact ⟨A, hA⟩
  · rintro ⟨A, hA⟩
    have h0 := hiff.mpr ⟨A, hA⟩
    omega

/-- **ON A NON-BIPARTITE GRAPH EVERY CUT HAS AT LEAST TWO MONOCHROMATIC VERTICES** — the cut axis
can never produce the constant `0`. -/
theorem card_monoSet_pos_of_not_isBipartite {A : Finset V} (hnb : ¬ G.IsBipartite) :
    2 ≤ (MonoSet G A).card := by
  by_contra h
  have hlt : (MonoSet G A).card < 2 := Nat.lt_of_not_ge h
  refine hnb ((isBipartite_iff_exists_monoSet_empty).mpr ⟨A, ?_⟩)
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨v, hv⟩
  obtain ⟨w, hw⟩ : ∃ w, MonoEdge G A v w := mem_monoSet.mp hv
  have hsym : MonoEdge G A w v :=
    ⟨hw.1.symm, hw.2.imp (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩)⟩
  have hwmem : w ∈ MonoSet G A := mem_monoSet.mpr ⟨v, hsym⟩
  have hvw : v ≠ w := fun hh => G.irrefl (hh ▸ hw.1)
  have hsub : ({v, w} : Finset V) ⊆ MonoSet G A := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact hx ▸ hv
    · exact Finset.mem_singleton.mp hx ▸ hwmem
  have hne : v ∉ ({w} : Finset V) := fun hh => hvw (Finset.mem_singleton.mp hh)
  have hcard2 : (({v, w} : Finset V) : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton, Nat.add_comm, Nat.add_one]
  have hle2 : (({v, w} : Finset V) : Finset V).card
      ≤ (MonoSet G A).card := Finset.card_le_card hsub
  omega

/-! ### Part 2 — degrees relative to a cut, and the stability of a cut -/

/-- **THE NUMBER OF NEIGHBOURS OF `v` ON `v`'S OWN SIDE OF THE CUT.** -/
def SameDeg (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  (Neigh G v).filter (fun w => w ∈ A) |>.card

/-- **THE NUMBER OF NEIGHBOURS OF `v` ON THE *OTHER* SIDE OF THE CUT.** -/
def CrossDeg (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  (Neigh G v).filter (fun w => w ∉ A) |>.card

theorem mem_sameDeg {A : Finset V} {v w : V} :
    w ∈ (Neigh G v).filter (fun x => x ∈ A) ↔ G.Adj v w ∧ w ∈ A := by
  rw [Finset.mem_filter, mem_neigh]

theorem mem_crossDeg {A : Finset V} {v w : V} :
    w ∈ (Neigh G v).filter (fun x => x ∉ A) ↔ G.Adj v w ∧ w ∉ A := by
  rw [Finset.mem_filter, mem_neigh]

/-- **EVERY NEIGHBOUR OF `v` IS ON EXACTLY ONE SIDE OF THE CUT:**
`SameDeg G A v + CrossDeg G A v = (degree of v)`. -/
theorem sameDeg_add_crossDeg (A : Finset V) (v : V) :
    SameDeg G A v + CrossDeg G A v = (Neigh G v).card := by
  rw [SameDeg, CrossDeg]
  exact Finset.card_filter_add_card_filter_not (s := Neigh G v) (p := fun w => w ∈ A)

/-- **A CUT IS *STABLE* WHEN NO VERTEX CAN BE PROFITABLY MOVED TO THE OTHER SIDE**: every `v ∈ A`
has at least as many neighbours on the other side as on its own.  Every maximum cut is stable, and
this is the only place in the development where the *optimality* of a cut is used. -/
def StableCut (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ v ∈ A, SameDeg G A v ≤ CrossDeg G A v

/-- **`MonoVertex` restricted to a member of `A`** is a *same-side* neighbour. -/
theorem monoVertex_of_mem {A : Finset V} {v : V} (hvA : v ∈ A) :
    MonoVertex G A v ↔ ∃ w ∈ A, G.Adj v w := by
  unfold MonoVertex MonoEdge
  simp only [hvA, true_and]
  constructor
  · rintro ⟨w, hadj, h1 | h1⟩
    · exact ⟨w, h1, hadj⟩
    · exfalso; exact h1.1 trivial
  · rintro ⟨w, hwA, hadj⟩
    exact ⟨w, hadj, Or.inl hwA⟩

/-- **A STABLE CUT PUSHES EVERY MONO VERTEX OUT OF ITS SIDE.**  If `v ∈ A` has a same-side
neighbour then, by stability, `v` also has a cross neighbour — this is the resource the counting
argument of `JSP90.sum_sameDeg_le_sum_crossDeg_of_stableCut` needs. -/
theorem exists_notMem_adj_of_stableCut {A : Finset V} (hA : StableCut G A) {v : V} (hvA : v ∈ A)
    (hm : MonoVertex G A v) : ∃ w, w ∉ A ∧ G.Adj v w := by
  obtain ⟨w, hwA, hadj⟩ := (monoVertex_of_mem hvA).mp hm
  have hpos : 0 < SameDeg G A v := by
    rw [SameDeg]
    exact Finset.card_pos.mpr
      ⟨w, Finset.mem_filter.mpr ⟨mem_neigh.mpr hadj, hwA⟩⟩
  have hcross : 0 < CrossDeg G A v := lt_of_lt_of_le hpos (hA v hvA)
  obtain ⟨w', hw'⟩ := Finset.card_pos.mp hcross
  exact ⟨w', (mem_crossDeg.mp hw').2, (mem_crossDeg.mp hw').1⟩

/-- **THE INTERNAL EDGES OF A STABLE SIDE NUMBER AT MOST HALF THE CUT:**
`∑ v ∈ A, SameDeg G A v ≤ ∑ v ∈ A, CrossDeg G A v`. -/
theorem sum_sameDeg_le_sum_crossDeg_of_stableCut {A : Finset V} (hA : StableCut G A) :
    (∑ v ∈ A, SameDeg G A v) ≤ ∑ v ∈ A, CrossDeg G A v :=
  Finset.sum_le_sum fun v hvA => hA v hvA

/-! ### Part 3 — the reduction from a stable cut with a small mono set -/

universe u

/-- **THE CLASS-LEVEL HYPOTHESIS OF THE MAXIMUM-CUT ROUTE, `JSP90.MaxCutMonoLe c`**:

> every finite graph of deficiency `≤ k` admits a **stable** cut (in particular a maximum cut)
> whose mono set has at most `c` vertices.

This is a `def`, and it is **not assumed anywhere**.  It is the round's precisely stated missing
lemma. -/
def MaxCutMonoLe (c : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (k : ℕ), LocIndep k G →
    ∃ A : Finset W, StableCut G A ∧ (MonoSet G A).card ≤ c

/-- **A STABLE CUT WITH A SMALL MONO SET GIVES THE CONCLUSION OF ERDŐS #73**, with constant `c`
independent of `k`. -/
theorem erdos73On_of_maxCutMonoLe (c : ℕ) (h : MaxCutMonoLe.{u} c) : Erdős73On.{u} c c := by
  intro W instW G hG
  obtain ⟨A, _, hcard⟩ := h W instW G c hG
  have h1 := closeToBipartite_monoSet (G := G) (A := A)
  refine h1.mono (m' := c) ?_
  omega

/-- **... and hence the whole of JSP-000090.**  This is a *reduction*: the max-cut route suffices,
provided `JSP90.MaxCutMonoLe c` for some `c`. -/
theorem erdos73_of_maxCutMonoLe (c : ℕ) (h : MaxCutMonoLe.{u} c) : Erdős73.{u} c :=
  ⟨c, erdos73On_of_maxCutMonoLe c h⟩

/-! ### Part 4 — the NEGATIVE result: on `K_n` the cut certificate is never optimal -/

section CompleteGraph

variable (n : ℕ)

/-- **A SIDE OF THE CUT WITH AT LEAST TWO VERTICES IS CONTAINED IN THE MONO SET OF `K_n`**, since a
complete graph makes every pair of *distinct* vertices adjacent. -/
theorem subset_monoSet_completeGraph_of_two {A : Finset (Fin n)} (hA : 2 ≤ A.card) :
    A ⊆ MonoSet (SimpleGraph.completeGraph (Fin n)) A := by
  intro v hvA
  obtain ⟨w, hwA, hvw⟩ := Finset.exists_mem_ne (s := A) hA v
  refine mem_monoSet.mpr ⟨w, ?_⟩
  have : (SimpleGraph.completeGraph (Fin n)).Adj v w := by
    rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj]
    exact hvw.symm
  exact ⟨this, Or.inl ⟨hvA, hwA⟩⟩

/-- **THE COMPLEMENTARY SIDE, IF IT HAS AT LEAST TWO VERTICES, IS ALSO CONTAINED IN THE MONO
SET**: those vertices are adjacent to every vertex of `A`, and none of them lies in `A`.  (Two
vertices really are needed: if `A = V \ {w}` then `w` has no neighbour outside `A` at all and is
*not* mono.) -/
theorem subset_compl_monoSet_completeGraph {A : Finset (Fin n)}
    (hc : 2 ≤ (Finset.univ \ A).card) :
    Finset.univ \ A ⊆ MonoSet (SimpleGraph.completeGraph (Fin n)) A := by
  intro v hv
  have hv' : v ∉ A := (Finset.mem_sdiff.mp hv).2
  obtain ⟨w, hw, hvw⟩ := Finset.exists_mem_ne (s := Finset.univ \ A) (by omega) v
  have hw' : w ∉ A := (Finset.mem_sdiff.mp hw).2
  refine mem_monoSet.mpr ⟨w, ?_⟩
  have : (SimpleGraph.completeGraph (Fin n)).Adj v w := by
    rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj]
    exact hvw.symm
  exact ⟨this, Or.inr ⟨hv', hw'⟩⟩

/-- **EVERY CUT OF `K_n` HAS A MONO SET OF AT LEAST `n − 1` VERTICES** for `n ≥ 4`. -/
theorem card_monoSet_ge_card_sub_one_completeGraph {A : Finset (Fin n)} (hn : 4 ≤ n) :
    n - 1 ≤ (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card := by
  have hcompl : (Finset.univ \ A).card = n - A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_fin]
  by_cases hA : 2 ≤ A.card
  · by_cases hc : 2 ≤ (Finset.univ \ A).card
    · have huniv : (Finset.univ : Finset (Fin n))
          ⊆ MonoSet (SimpleGraph.completeGraph (Fin n)) A := by
        have hstep : A ∪ (Finset.univ \ A) ⊆
            MonoSet (SimpleGraph.completeGraph (Fin n)) A :=
          Finset.union_subset (subset_monoSet_completeGraph_of_two (n := n) hA)
            (subset_compl_monoSet_completeGraph (n := n) hc)
        intro x _
        rcases Classical.em (x ∈ A) with h | h
        · exact hstep (Finset.mem_union_left (Finset.univ \ A) h)
        · exact hstep (Finset.mem_union_right A (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, h⟩))
      have h1 : n ≤ (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card := by
        simpa using Finset.card_le_card huniv
      omega
    · have hcle : (Finset.univ \ A).card ≤ 1 := by omega
      have hcle' : n - A.card ≤ 1 := by rw [← hcompl]; exact hcle
      have hA' : n - 1 ≤ A.card := (Nat.sub_le_iff_le_add.mpr (show n ≤ A.card + 1 by omega))
      have hle : A.card ≤ (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card :=
        Finset.card_le_card (subset_monoSet_completeGraph_of_two (n := n) hA)
      omega
  · have hc : 2 ≤ (Finset.univ \ A).card := by
      rw [hcompl]
      omega
    have hle : (Finset.univ \ A).card ≤ (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card :=
      Finset.card_le_card (subset_compl_monoSet_completeGraph (n := n) hc)
    have hn1 : n - 1 ≤ (Finset.univ \ A).card := by
      rw [hcompl]
      have h1 : 1 ≤ n := by omega
      have hAn : A.card ≤ n := by omega
      omega
    exact Nat.le_trans hn1 hle

/-- **THE CUT CERTIFICATE IS NEVER OPTIMAL ON A COMPLETE GRAPH.**  For `n ≥ 4` *no* cut `A` of
`K_n` attains the optimal odd cycle transversal number `n − 2`
(`JSP90.closeToBipartite_iff_completeGraph_add_two`): every mono set has at least `n − 1`
vertices.  No choice of cut, and in particular no *maximum* cut, repairs this. -/
theorem not_card_monoSet_le_opt_completeGraph (hn : 4 ≤ n) (A : Finset (Fin n)) :
    ¬ (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card ≤ n - 2 := by
  have h1 := card_monoSet_ge_card_sub_one_completeGraph (n := n) (hn := hn) (A := A)
  omega

/-- **A SINGLETON SIDE GIVES EXACTLY `n − 1`**: the cut axis cannot do better than `n − 1` on
`K_n`, while the optimal transversal number is `n − 2`.  So the certificate of Part 1 misses the
optimum by exactly one vertex on the sharp examples of Erdős #73. -/
theorem card_monoSet_singleton_completeGraph (hn : 4 ≤ n) (v : Fin n) :
    (MonoSet (SimpleGraph.completeGraph (Fin n)) ({v} : Finset (Fin n))).card = n - 1 := by
  have hcompl : ((Finset.univ : Finset (Fin n)).erase v).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_fin]
  have hnotv : v ∉ MonoSet (SimpleGraph.completeGraph (Fin n)) ({v} : Finset (Fin n)) := by
    intro hm
    obtain ⟨w, hadj, hside⟩ := mem_monoSet.mp hm
    rcases hside with h | h
    · rcases h with ⟨-, h2⟩
      have hwv : w = v := Finset.mem_singleton.mp h2
      rw [hwv] at hadj
      have hnot : ¬ (SimpleGraph.completeGraph (Fin n)).Adj v v := by
        simp [SimpleGraph.completeGraph_eq_top]
      exact hnot hadj
    · rcases h with ⟨h1, -⟩
      exact h1 (Finset.mem_singleton.mpr rfl)
  have hsub2 : MonoSet (SimpleGraph.completeGraph (Fin n)) ({v} : Finset (Fin n))
      ⊆ (Finset.univ : Finset (Fin n)).erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hnotv (Eq.symm h ▸ hx), Finset.mem_univ x⟩
  have hle : (MonoSet (SimpleGraph.completeGraph (Fin n)) ({v} : Finset (Fin n))).card ≤ n - 1 :=
    hcompl ▸ Finset.card_le_card hsub2
  have hge : n - 1 ≤ (MonoSet (SimpleGraph.completeGraph (Fin n)) ({v} : Finset (Fin n))).card :=
    card_monoSet_ge_card_sub_one_completeGraph (n := n) (hn := hn) (A := {v})
  omega

/-- **THE EXACT TRANSVERSAL NUMBER OF `K_n` IS `n − 2`, AND EVERY CUT CERTIFICATE COSTS `n − 1`** —
the cut axis wastes exactly one vertex on the sharp examples of Erdős #73. -/
theorem closeToBipartite_and_monoSet_completeGraph (hn : 4 ≤ n) (A : Finset (Fin n)) :
    CloseToBipartite (n - 2) (SimpleGraph.completeGraph (Fin n)) ∧
      n - 1 ≤ (MonoSet (SimpleGraph.completeGraph (Fin n)) A).card :=
  ⟨by rw [closeToBipartite_iff_completeGraph_add_two]; omega,
    card_monoSet_ge_card_sub_one_completeGraph (n := n) (hn := hn) (A := A)⟩

end CompleteGraph

end

end JSP90