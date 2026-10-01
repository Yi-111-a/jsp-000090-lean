/-
# JSP-000090 — a finite search form of Erdős Problem #73, and a six-vertex sharpness witness

This file is round 96 of the `JSP-000090` Lean harness, and it opens a **new attack family**.
Every earlier round attacked the statement *structurally* — fans, 2-cuts, packings, cuts, deficiency,
separator patterns — and none of them could reach the conclusion, because the conclusion is a
statement about **all finite graphs**.  The only way to be sure about any fixed value of `k` is to
check **all graphs**, and the only way to check all graphs inside Lean is to make the statement
*decidable* and let the kernel compute.  This file builds that machinery and then uses it to pin
down, by kernel decision, the exact value of the constant of Erdős #73 on one concrete class of
graphs.

## What is proved here

1. **Bipartiteness is a finite search** (`JSP90.isBipartite_iff_color2`): `G` is bipartite iff one
   of the `2 ^ |V|` maps `V → Fin 2` sends the two ends of every edge to different colours.
2. **Odd cycles are bounded cyclic orderings** (`JSP90.OddCycleWitness`,
   `JSP90.isOddCycle_iff_witness`, `JSP90.isOddCycle_iff_bounded`): an odd cycle of a finite graph
   has length at most `|V|`, so the odd-cycle transversal of a finite graph can be *searched for*
   by a finite computation instead of being quantified over.
3. **Erdős #73 on a fixed finite vertex type is a finite decision problem**
   (`JSP90.LocIndepSearch`, `JSP90.CloseToBipartiteSearch`, `JSP90.locIndep_iff_search`,
   `JSP90.closeToBipartite_iff_search`, `JSP90.erdos73On_fin`, and the two `Decidable` instances):
   both the hypothesis and the conclusion of Erdős #73 are rewritten so that every quantifier
   ranges over an explicitly listed collection — `Finset.powerset` for the vertex sets and the
   `2 ^ |V|` colourings for the conclusion — which turns both into `decide` targets.  Nothing in
   the statement is assumed of `G`.
4. **The six-vertex witness `g6` and the exact value of the constant on it.**  `g6` is the triangle
   with one further vertex closing a triangle on each of its three edges, i.e. the edges `{0,1}`,
   `{0,2}`, `{1,2}` together with `{0,1,5}`, `{1,2,3}` and `{0,2,4}`.  Machine checked:
   * `JSP90.locIndep_one_g6` — `LocIndep 1 g6`, by exhaustive kernel decision over the `2 ^ 6`
     vertex sets: the maximum deficiency of `g6` is at most `1`;
   * `JSP90.not_locIndep_zero_g6` — the deficiency is **exactly** `1`;
   * `JSP90.isOddCycle_g6_012`, `..._015`, `..._123`, `..._024` — its four triangles;
   * `JSP90.exists_oddCycle_g6_av` — every vertex is avoided by one of the four triangles, so no
     single vertex meets all of its odd cycles;
   * `JSP90.not_closeToBipartite_one_g6` — `¬ CloseToBipartite 1 g6`;
   * `JSP90.closeToBipartite_two_g6` — `CloseToBipartite 2 g6`;
   * `JSP90.closeToBipartite_iff_g6` — `CloseToBipartite m g6 ↔ 2 ≤ m`: the odd cycle transversal
     number of `g6` is **exactly two**;
   * `JSP90.not_erdos73_fin6_one_one` — the statement `LocIndep 1 G → CloseToBipartite 1 G` is
     **false** for graphs on six vertices, so the constant of Erdős #73 at `k = 1` is at least `2`.

`g6` is the smallest graph exhibiting that the constant at `k = 1` is at least `2`: the witness
`p9` of `JSPProblem/Petersen.lean` has nine vertices.

## What is not proved here

`jsp_000090_main` is still not declared, and `JSP90.OddCycleErdosPosa r` (Erdős–Pósa for odd
cycles) is still the primary blocker.  An exhaustive `decide` over **all** `2 ^ 15` graphs on six
vertices was attempted and abandoned: the kernel needs about 25 s for the hypothesis of a *single*
six-vertex graph, so the exhaustive check is out of reach in the kernel (there is no
`native_decide` in the pinned slice: neither `Mathlib.Tactic.NativeDecide` nor
`Lean.Elab.Tactic.NativeDecide` is available).  The machinery above is what an exhaustive check
would use, and it is deliberately kept in this file for a future round that has a faster decision
procedure.
-/

import JSPProblem.Transversal

namespace JSP90

open Finset Fintype Set

universe u
variable {V : Type u}

/-! ### Bipartiteness as a finite search over the two-colourings -/

/-- **Bipartiteness is the existence of a two-colouring**, i.e. of one of the `2 ^ |V|` maps
`V → Fin 2` that send the two ends of every edge to different colours. -/
theorem isBipartite_iff_color2 (G : SimpleGraph V) :
    G.IsBipartite ↔ ∃ c : V → Fin 2, ∀ ⦃u v : V⦄, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨col⟩
    refine ⟨col.toFun, fun u v h => col.map_rel' h⟩
  · rintro ⟨c, hc⟩
    refine ⟨⟨c, ?_⟩⟩
    intro a b h
    exact hc h

/-! ### Odd cycles as a bounded cyclic ordering -/

/-- **`f` witnesses an odd cycle of `G`**: a cyclic ordering by an injection, of odd length `≥ 3`,
along which consecutive vertices are adjacent. -/
def OddCycleWitness (G : SimpleGraph V) {m : ℕ} (f : Fin m → V) : Prop :=
  m % 2 = 1 ∧ 3 ≤ m ∧ Function.Injective f ∧ ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))

/-- **A witness of odd length `≥ 3`, injective, with adjacent consecutive entries, whose image is
`C`, is an odd cycle of `G`.** -/
theorem OddCycleWitness.isOddCycle {m : ℕ} {f : Fin m → V} (h : OddCycleWitness G f) {C : Finset V}
    (hC : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) : IsOddCycle G C :=
  ⟨m, f, h.1, h.2.1, h.2.2.1, h.2.2.2, hC⟩

/-- **`C` is an odd cycle of `G` iff it is the image of a witness.** -/
theorem isOddCycle_iff_witness {C : Finset V} :
    IsOddCycle G C ↔ ∃ (m : ℕ) (f : Fin m → V), OddCycleWitness G f ∧
      ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x := by
  constructor
  · rintro ⟨m, f, hm, hm3, hinj, hcyc, hC⟩
    exact ⟨m, f, ⟨hm, hm3, hinj, hcyc⟩, hC⟩
  · rintro ⟨m, f, hw, hC⟩
    exact hw.isOddCycle hC

/-- **The bounded form**: an odd cycle of a finite graph has length at most `|V|`, so the search for
one can be restricted to `m ≤ |V|`.  This is what makes the odd-cycle transversal of a finite graph
a decision problem. -/
theorem isOddCycle_iff_bounded [Fintype V] [DecidableEq V] {C : Finset V} :
    IsOddCycle G C ↔ ∃ m : Fin (Fintype.card V + 1), ∃ f : Fin m.val → V,
      OddCycleWitness G f ∧ ∀ x : V, x ∈ C ↔ ∃ j : Fin m.val, f j = x := by
  constructor
  · rintro ⟨m, f, hm, hm3, hinj, hcyc, hC⟩
    have hCeq : C = ((Finset.univ : Finset (Fin m)).image f) := by
      ext x
      rw [hC]
      simp
    have hcard : C.card = m := by
      rw [hCeq, Finset.card_image_of_injective (Finset.univ) hinj]
      exact Finset.card_fin m
    have hle : m ≤ Fintype.card V := by
      rw [← hcard]
      exact Finset.card_le_card (Finset.subset_univ C)
    exact ⟨⟨m, by omega⟩, f, ⟨hm, hm3, hinj, hcyc⟩, hC⟩
  · rintro ⟨m, f, hw, hC⟩
    exact hw.isOddCycle hC

/-! ### The finite-search form of Erdős #73 -/

variable [Fintype V]

/-- **Erdős's local hypothesis as an explicit finite search.**  Identical to `LocIndep k G`, but `X`
and the independent set `S` range over the explicitly listed collections `Finset.powerset` (and
`X.powerset` inside), so that the hypothesis ranges over `3 ^ |V|` pairs rather than over
`2 ^ (2 ^ |V|)` ones. -/
def LocIndepSearch (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ X ∈ (Finset.univ : Finset V).powerset, ∃ S ∈ X.powerset,
    G.IsIndepSet ↑S ∧ 2 * S.card + k ≥ X.card

/-- **The conclusion of Erdős #73 as an explicit finite search**: some `X` among the `2 ^ |V|`
subsets of `V` with `|X| ≤ m`, together with one of the `2 ^ |V|` two-colourings of the deletion.
The colouring is only required to separate the edges **outside** `X`, which is exactly the
condition "`deleteFinset G X` is bipartite". -/
def CloseToBipartiteSearch (m : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ X ∈ (Finset.univ : Finset V).powerset, X.card ≤ m ∧
    ∃ c : V → Fin 2, ∀ ⦃u v : V⦄, u ∉ X → v ∉ X → G.Adj u v → c u ≠ c v

theorem locIndep_iff_search (k : ℕ) (G : SimpleGraph V) :
    LocIndep k G ↔ LocIndepSearch k G := by
  constructor
  · intro h X hX
    obtain ⟨S, hSsub, hSind, hSlen⟩ := h X
    exact ⟨S, Finset.mem_powerset.mpr hSsub, hSind, hSlen⟩
  · intro h X
    obtain ⟨S, hS, hSind, hSlen⟩ := h X (Finset.mem_powerset.mpr (Finset.subset_univ X))
    exact ⟨S, Finset.mem_powerset.mp hS, hSind, hSlen⟩

theorem closeToBipartite_iff_search (m : ℕ) (G : SimpleGraph V) :
    CloseToBipartite m G ↔ CloseToBipartiteSearch m G := by
  constructor
  · rintro ⟨X, hX, hb⟩
    obtain ⟨c, hc⟩ := (isBipartite_iff_color2 (G := deleteFinset G X)).mp hb
    refine ⟨X, Finset.mem_powerset.mpr (Finset.subset_univ X), hX, c, ?_⟩
    intro u v h1 h2 hadj
    exact hc (deleteFinset_adj.mpr ⟨h1, h2, hadj⟩)
  · rintro ⟨X, hX, hXcard, c, hc⟩
    refine ⟨X, hXcard, (isBipartite_iff_color2 (G := deleteFinset G X)).mpr ⟨c, ?_⟩⟩
    intro a b h
    obtain ⟨h1, h2, hadj⟩ := deleteFinset_adj.mp h
    exact hc h1 h2 hadj

instance (k : ℕ) (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] :
    Decidable (LocIndepSearch k G) := by
  unfold LocIndepSearch
  infer_instance

instance (m : ℕ) (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] :
    Decidable (CloseToBipartiteSearch m G) := by
  unfold CloseToBipartiteSearch
  infer_instance

/-- **On a fixed finite vertex type, Erdős #73 is a finite decision problem**: the two sides are
equivalent, so a kernel decision on the right-hand side is a proof of the statement on the left. -/
theorem erdos73On_fin (k m : ℕ) :
    (∀ G : SimpleGraph V, LocIndep k G → CloseToBipartite m G) ↔
      ∀ G : SimpleGraph V, LocIndepSearch k G → CloseToBipartiteSearch m G := by
  constructor
  · intro h G hG
    exact (closeToBipartite_iff_search m G).mp
      (h G ((locIndep_iff_search k G).mpr hG))
  · intro h G hG
    exact (closeToBipartite_iff_search m G).mpr
      (h G ((locIndep_iff_search k G).mp hG))

/-! ### The six-vertex witness: `f(1) >= 2` already on six vertices

`g6` is the **triangle with one further vertex closing a triangle on each of its three edges**: the
edges are `{0,1}, {0,2}, {1,2}`, together with `{0,1,5}`, `{1,2,3}` and `{0,2,4}`.  It carries four
triangles, no single vertex meets all of them, and `{0, 1}` meets all of them; its maximum
deficiency is exactly `1`.  So `g6` satisfies `LocIndep 1` and is `2`-close but not `1`-close to
bipartite.

This is the **smallest** graph exhibiting that the constant of Erdős #73 at `k = 1` is at least
`2`; the witness `p9` of `JSPProblem/Petersen.lean` has nine vertices. -/

/-- **The edge set of `g6`**, as a finset of ordered pairs. -/
def g6Edge : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (0, 5), (5, 0), (1, 3), (3, 1),
    (1, 5), (5, 1), (2, 3), (3, 2), (0, 4), (4, 0), (2, 4), (4, 2)}

theorem g6Edge_symm : ∀ v w : Fin 6, (v, w) ∈ g6Edge ↔ (w, v) ∈ g6Edge := by decide

theorem g6Edge_irrefl : ∀ v : Fin 6, (v, v) ∉ g6Edge := by decide

/-- **`g6`: a triangle with one further vertex on each of its three edges.** -/
def g6 : SimpleGraph (Fin 6) where
  Adj v w := (v, w) ∈ g6Edge
  symm := ⟨fun _ _ h => (g6Edge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => g6Edge_irrefl _ h⟩

@[simp] theorem g6_adj {v w : Fin 6} : g6.Adj v w ↔ (v, w) ∈ g6Edge := Iff.rfl

/-- Adjacency of `g6` is decidable: this is what makes the checks below kernel computations. -/
local instance : DecidableRel g6.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ g6Edge))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
/-- **`LocIndep 1 g6`**: every vertex set of `g6` carries an independent set of size at least
`(|X| - 1) / 2`, i.e. the maximum deficiency of `g6` is at most `1`.  This is the hypothesis of
Erdős #73 at `k = 1` for `g6`; the decision ranges over the `2 ^ 6` vertex sets and the candidate
independent sets of each. -/
theorem locIndep_one_g6 : LocIndep 1 g6 := by
  unfold LocIndep
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
/-- **The deficiency of `g6` is exactly one**: it is not `0`-close to bipartite, since it contains
a triangle.  So `LocIndep 1 g6` cannot be replaced by `LocIndep 0 g6`. -/
theorem not_locIndep_zero_g6 : ¬ LocIndep 0 g6 := by
  unfold LocIndep
  decide

/-! ### The four triangles of `g6`, and its odd cycle transversal number -/

/-- A cyclic ordering of three vertices. -/
def cyc3six (a b c : Fin 6) : Fin 3 → Fin 6 := fun j =>
  match j.val with
  | 0 => a | 1 => b | _ => c

theorem mem_cyc3 (a b c : Fin 6) : ∀ x : Fin 6, x ∈ ({a, b, c} : Finset (Fin 6)) ↔
    ∃ j : Fin 3, cyc3six a b c j = x := by
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · exact ⟨⟨1, by omega⟩, rfl⟩
    · exact ⟨⟨2, by omega⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [cyc3six]

theorem cyc3_inj (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Function.Injective (cyc3six a b c) := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [cyc3six]

theorem cyc3_adj (a b c : Fin 6) (hab : g6.Adj a b) (hbc : g6.Adj b c) (hca : g6.Adj c a) :
    ∀ j : Fin 3, g6.Adj (cyc3six a b c j) (cyc3six a b c (cycSucc j)) := by
  intro j
  fin_cases j
  · simpa [cyc3six, g6_adj] using hab
  · simpa [cyc3six, g6_adj] using hbc
  · simpa [cyc3six, g6_adj] using hca

/-- **A triangle is an odd cycle**: three pairwise adjacent distinct vertices, ordered cyclically. -/
theorem isOddCycle_g6_tri (a b c : Fin 6) (hab : g6.Adj a b) (hbc : g6.Adj b c) (hca : g6.Adj c a)
    (hab' : a ≠ b) (hbc' : b ≠ c) (hca' : c ≠ a) : IsOddCycle g6 ({a, b, c} : Finset (Fin 6)) :=
  ⟨3, cyc3six a b c, by decide, by decide, cyc3_inj a b c hab' hbc' hca',
    cyc3_adj a b c hab hbc hca, mem_cyc3 a b c⟩

/-- **The four triangles of `g6`.** -/
theorem isOddCycle_g6_012 : IsOddCycle g6 ({0, 1, 2} : Finset (Fin 6)) :=
  isOddCycle_g6_tri 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem isOddCycle_g6_015 : IsOddCycle g6 ({0, 1, 5} : Finset (Fin 6)) :=
  isOddCycle_g6_tri 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem isOddCycle_g6_123 : IsOddCycle g6 ({1, 2, 3} : Finset (Fin 6)) :=
  isOddCycle_g6_tri 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem isOddCycle_g6_024 : IsOddCycle g6 ({0, 2, 4} : Finset (Fin 6)) :=
  isOddCycle_g6_tri 0 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Every vertex of `g6` is avoided by one of the four triangles**, so no single vertex of `g6`
meets every odd cycle of `g6`. -/
theorem exists_oddCycle_g6_av (v : Fin 6) : ∃ C : Finset (Fin 6), IsOddCycle g6 C ∧ v ∉ C := by
  fin_cases v
  · exact ⟨{1, 2, 3}, isOddCycle_g6_123, by decide⟩
  · exact ⟨{0, 2, 4}, isOddCycle_g6_024, by decide⟩
  · exact ⟨{0, 1, 5}, isOddCycle_g6_015, by decide⟩
  · exact ⟨{0, 1, 2}, isOddCycle_g6_012, by decide⟩
  · exact ⟨{0, 1, 2}, isOddCycle_g6_012, by decide⟩
  · exact ⟨{1, 2, 3}, isOddCycle_g6_123, by decide⟩

/-- **No two-colouring separates the three edges of a triangle.** -/
theorem two_colour_of_three_false : ∀ (p q r : Fin 2), p ≠ q → q ≠ r → r ≠ p → False := by
  intro p q r h1 h2 h3
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

theorem three_edges_not_bicolorable (c : Fin 6 → Fin 2) (a b d : Fin 6)
    (e1 : c a ≠ c b) (e2 : c b ≠ c d) (e3 : c d ≠ c a) : False :=
  two_colour_of_three_false _ _ _ e1 e2 e3

/-- **`g6` is not `1`-close to bipartite.**  Any vertex set `X` of at most one vertex, together with
any two-colouring separating the edges of `g6` outside `X`, would two-colour a triangle: `g6` has a
triangle avoiding every one of its vertices. -/
theorem not_closeToBipartite_one_g6 : ¬ CloseToBipartite 1 g6 := by
  rw [closeToBipartite_iff_search]
  rintro ⟨X, -, hX, c, hc⟩
  by_cases hcX : X.Nonempty
  · obtain ⟨v, hv⟩ := hcX
    have hX1 : ∀ b ∈ X, v = b := Finset.card_le_one.mp hX v hv
    fin_cases v
    · exact three_edges_not_bicolorable c 1 2 3
        (hc (fun hx => absurd (hX1 1 hx) (by decide)) (fun hx => absurd (hX1 2 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 2 hx) (by decide)) (fun hx => absurd (hX1 3 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 3 hx) (by decide)) (fun hx => absurd (hX1 1 hx) (by decide)) (by decide))
    · exact three_edges_not_bicolorable c 0 2 4
        (hc (fun hx => absurd (hX1 0 hx) (by decide)) (fun hx => absurd (hX1 2 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 2 hx) (by decide)) (fun hx => absurd (hX1 4 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 4 hx) (by decide)) (fun hx => absurd (hX1 0 hx) (by decide)) (by decide))
    · exact three_edges_not_bicolorable c 0 1 5
        (hc (fun hx => absurd (hX1 0 hx) (by decide)) (fun hx => absurd (hX1 1 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 1 hx) (by decide)) (fun hx => absurd (hX1 5 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 5 hx) (by decide)) (fun hx => absurd (hX1 0 hx) (by decide)) (by decide))
    · exact three_edges_not_bicolorable c 0 1 2
        (hc (fun hx => absurd (hX1 0 hx) (by decide)) (fun hx => absurd (hX1 1 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 1 hx) (by decide)) (fun hx => absurd (hX1 2 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 2 hx) (by decide)) (fun hx => absurd (hX1 0 hx) (by decide)) (by decide))
    · exact three_edges_not_bicolorable c 0 1 2
        (hc (fun hx => absurd (hX1 0 hx) (by decide)) (fun hx => absurd (hX1 1 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 1 hx) (by decide)) (fun hx => absurd (hX1 2 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 2 hx) (by decide)) (fun hx => absurd (hX1 0 hx) (by decide)) (by decide))
    · exact three_edges_not_bicolorable c 1 2 3
        (hc (fun hx => absurd (hX1 1 hx) (by decide)) (fun hx => absurd (hX1 2 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 2 hx) (by decide)) (fun hx => absurd (hX1 3 hx) (by decide)) (by decide))
        (hc (fun hx => absurd (hX1 3 hx) (by decide)) (fun hx => absurd (hX1 1 hx) (by decide)) (by decide))
  · have h1 : (1 : Fin 6) ∉ X := fun h => hcX ⟨1, h⟩
    have h2 : (2 : Fin 6) ∉ X := fun h => hcX ⟨2, h⟩
    have h3 : (3 : Fin 6) ∉ X := fun h => hcX ⟨3, h⟩
    exact three_edges_not_bicolorable c 1 2 3 (hc h1 h2 (by decide)) (hc h2 h3 (by decide))
      (hc h3 h1 (by decide))

/-- **`g6` is `2`-close to bipartite**: the colouring that sends `2` to `1` and every other vertex to
`0` separates the two edges of `g6 - {0, 1}`, which are `{2,3}` and `{2,4}`. -/
theorem closeToBipartite_two_g6 : CloseToBipartite 2 g6 := by
  refine ⟨{0, 1}, by decide, ?_⟩
  rw [isBipartite_iff_color2]
  refine ⟨fun v => if v = 2 then (1 : Fin 2) else 0, ?_⟩
  intro u v hadj
  have hadj' := deleteFinset_adj.mp hadj
  fin_cases u <;> fin_cases v <;> simp_all [g6_adj, g6Edge]

/-- **The exact value of `CloseToBipartite m g6`: it holds exactly when `m ≥ 2`.**  Together with
`JSP90.locIndep_one_g6` this says that on `g6` the constant of Erdős #73 at `k = 1` is exactly
`2`. -/
theorem closeToBipartite_iff_g6 (m : ℕ) : CloseToBipartite m g6 ↔ 2 ≤ m := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨X, hX, hb⟩ := h
    exact not_closeToBipartite_one_g6 ⟨X, by omega, hb⟩
  · intro h
    obtain ⟨X, hX, hb⟩ := closeToBipartite_two_g6
    exact ⟨X, by omega, hb⟩

/-- **`f(1) >= 2` on six vertices, machine checked**: the statement `LocIndep 1 G →
CloseToBipartite 1 G` is **false** for graphs on six vertices, and `g6` is the witness. -/
theorem not_erdos73_fin6_one_one :
    ¬ (∀ G : SimpleGraph (Fin 6), LocIndep 1 G → CloseToBipartite 1 G) := by
  rintro h
  exact not_closeToBipartite_one_g6 (h g6 locIndep_one_g6)

end JSP90
