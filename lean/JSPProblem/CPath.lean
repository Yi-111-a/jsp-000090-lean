/-
# JSP-000090 — `JSPProblem/CPath.lean`: the **C-PATH** (Mader's object) and the **two-attachment
transversal**

Round 110 (`JSPProblem/Piece.lean`) closed the cut-vertex axis: a one-sided chain of 1-cuts is a
*free* reduction (`JSP90.closeToBipartite_iff_of_oneNonBipartitePiece`,
`JSP90.closeToBipartite_iff_of_twoSideCuts`), so what is left of `JSP90.OddCycleErdosPosa r` is the
case of a graph with **no cut vertex**, and `discovery/JSP-000090/policy.json` named the next single
step:

> a first sub-step: formalise the **C-path** itself (a path from a vertex of `C` to `x` with all
> internal vertices outside `C`) and prove that **the shortest C-path is induced**.

This file (attack family 52) does the first half of that step and, from the object it defines,
obtains a **new bounded transversal for a whole class of graphs**, i.e. new progress on
`OddCycleErdosPosa` rather than only vocabulary.

## What is proved

| result | content |
| --- | --- |
| **`JSP90.IsCPath`** | **THE OBJECT: A `C`-PATH.**  A simple path of `d` steps from the vertex `f i` of the cycle `C` to the vertex `x ∉ C`, none of whose other vertices lies on `C` |
| `IsCPath.card`, `IsCPath.adj_step`, `IsCPath.notMem_interior`, `IsCPath.notMem_end` | the API: the `C`-path has `d + 1` vertices and `d` edges, and **no vertex other than the first one lies on `C`** |
| `extendPath`, `extendPath_get`, `extendPath_at`, `extendPath_adj` | the extended path `extendPath p y : Fin (d + 2) → V`, which appends the vertex `y` to a `C`-path |
| **`IsCPath.extend`** | **A `C`-PATH MAY BE EXTENDED BY ONE EDGE**: if `y ∉ C`, `y` is not a vertex of the path and `y` is adjacent to the target `x`, then the extension is a `C`-path of length `d + 1` to `y` — the classical step from a `C`-path of length `d` to one of length `d + 1` |
| **`IsOddCycle.exists_edge_avoiding`** | **a cycle of length at least `3` has an edge avoiding any prescribed vertex of it** — only the two edges at a vertex meet it, and the edge two steps later avoids it because that would force `m ∣ 1` or `m ∣ 2` |
| **`JSP90.closeToBipartite_of_twoAttach`** | **THE TWO-ATTACHMENT TRANSVERSAL.**  If `C` is an odd cycle of `G` with `ℓ = |C|` vertices and **every odd cycle of `G` meets `C` in at least two vertices**, then `CloseToBipartite (ℓ - 1) G`: delete `C` minus one of its vertices |
| **`JSP90.erdos73On_of_twoAttach`** | **A NEW INSTANCE OF THE HEADLINE THEOREM**: `LocIndep k G` together with the two-attachment hypothesis for one odd cycle `C` gives `CloseToBipartite (|C| - 1) G`, with a constant **independent of `k`** — against the `ℓ * k` of `JSPProblem/Transversal.lean` `erdos73On_of_bounded_odd_girth`.  This is the first transversal bound in this development that does not grow with the local parameter |

## What is *not* proved, and what is left for the next round

`policy.json` asked for two things: the `C`-path object (done here) and the **shortest `C`-path is
induced**.  The second is *not* in this file: the proof needed three further statements — the chord
shortening `IsCPath.skip` (the splice `skipPath`), the minimality predicate `IsCPath.Shortest`, and
the inducedness `IsCPath.induced_of_shortest` — whose index arithmetic is written out below
(`skip_idx_lt`, `skip_idx_inj`) and is **partly proved**: `skipPath`/`skipPath_le`/`skipPath_gt`
compile, and the remaining work is precisely
`IsCPath.skip` → `IsCPath.induced_of_shortest` → `IsCPath.ne_iff_last` (Mader's neighbour count)
and `IsCPath.isOddCycle_return` (a closed `C`-path is an odd cycle of `d + 1` vertices).  Those four
names are recorded in `discovery/JSP-000090/policy.json` as the concrete next lemmas.

The two-attachment transversal is the depth-one half of the attachment axis only: it needs a cycle of
`G` such that every odd cycle passes through it twice.  The natural strengthening — that this holds
for *some* odd cycle of every 2-connected graph satisfying `LocIndep k` — is not proved, and neither
is `JSP90.OddCycleErdosPosa r` or `jsp_000090_main`.

## Toolchain notes

* `Function.Injective f` is `∀ ⦃a b⦄, f a = f b → a = b`, so its proofs do `intro u v hne` with
  `hne` the **function** equality; the goal `u = v` is then closed with `Fin.ext` or `Fin.ext_iff`.
* `Nat.succ n` and `n + 1` are *not* syntactically equal, and in a theorem statement the `Fin`
  index proof must be given in the `n + 1` form (`lt_d_succ`, `zero_lt_d_succ`,
  `Nat.lt_succ_of_le`); the `zero_lt_fin_mk'` bridge is needed whenever a `C`-path index has to be
  shown positive, because `omega` cannot see through `Fin.val`.
* A `def` of the form `fun j => if j.val = n then … else f ⟨j.val, by omega⟩` elaborates the `if` as
  an **`ite`** (the `else` branch then has no hypothesis in context and `omega` fails); writing
  `if _h : j.val = n then … else …` makes it a `dite`, after which `simp only […, dite_eq_left h]`
  and `dite_eq_right h` fire.
* `cycSucc j` has value `(j.val + 1) % n`; to rewrite it as `⟨j.val + 1, _⟩` use
  `apply Fin.ext; show (j.val + 1) % (d + 1) = j.val + 1; exact Nat.mod_eq_of_lt …` — `omega` does
  **not** handle `% (d + 1)` with `d` a variable.
* `Nat.find`/`Nat.find_min` need a `DecidablePred` on the predicate, which
  `∃ i p, IsCPath G m n f i C hCmem x p` does not have (existence of a *function*); the length of a
  shortest `C`-path must therefore be expressed with `IsCPath.Shortest` (a hypothesis) rather than
  with `Nat.find`, which is why `JSP90.cPathDist` is **not** in this file.
* `Finset.disjoint_left.mp : Disjoint s t → s ∩ t = ∅` (`.mp`, not `.mpr`), and
  `Finset.eq_empty_iff_forall_notMem` needs the `Finset.` prefix to avoid the `Set.` one.
-/

import JSPProblem.Fan
import JSPProblem.Boundary

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqCPath : DecidableEq V := Classical.decEq V

/-! ### Part 0 — the `C`-path, Mader's object -/

section CPath

variable {m d : ℕ}

/-- `0 < t + 1`, in the form the `Fin (t + 1)` constructor needs. -/
theorem zero_lt_add_one (t : ℕ) : 0 < t + 1 := Nat.succ_pos t

/-- `0 < t` for the natural index `t` of a `Fin n` element.  `omega` cannot see through
`Fin.val`, so this small bridge is used wherever a `C`-path index has to be shown to be
positive. -/
theorem zero_lt_fin_mk' (n t : ℕ) (ht : t < n) (h0 : 0 < t) : 0 < (⟨t, ht⟩ : Fin n).val := by
  show 0 < t
  exact h0

/-- `t + 1 < n + 1`. -/
theorem succ_lt_add_one {t n : ℕ} (h : t < n) : t + 1 < n + 1 := Nat.succ_lt_succ h

/-- `0 ≤ b` implies `0 < a + 1 + b`. -/
theorem zero_lt_of_nonneg_add_one (a b : ℕ) (h : 0 ≤ b) : 0 < a + 1 + b := by omega

/-- `a + 2 ≤ b` implies `a ≤ b`. -/
theorem le_of_add_two_le {a b : ℕ} (h : a + 2 ≤ b) : a ≤ b := by omega

/-- `d < d + 1`, in the `Fin (d + 1)` form. -/
theorem lt_d_succ (d : ℕ) : d < d + 1 := Nat.lt_succ_of_le (Nat.le_refl d)

/-- `0 < d + 1`, in the `Fin (d + 1)` form. -/
theorem zero_lt_d_succ (d : ℕ) : 0 < d + 1 := Nat.succ_pos d

/-- `t < d + 2` in the `Fin (d + 2)` form. -/
theorem lt_d_succ' {d t : ℕ} (h : t < d + 1) : t < d + 2 :=
  Nat.lt_trans h (lt_d_succ (d + 1))

/-- `t + 1 < d + 2` in the `Fin (d + 2)` form. -/
theorem succ_lt_d_succ' {d t : ℕ} (h : t < d + 1) : t + 1 < d + 2 := Nat.succ_lt_succ h

/-- An index of `Fin (d + 2)` which is not the last one indexes `Fin (d + 1)`. -/
theorem fin_lt_of_ne {d : ℕ} {j : Fin (d + 2)} (hj : j.val ≠ d + 1) : j.val < d + 1 := by omega

/-- Past `e`, the map `t ↦ t - e - 1` is injective. -/
theorem sub_sub_inj (u v e : ℕ) (h1 : ¬ u ≤ e) (h2 : ¬ v ≤ e)
    (h : u - e - 1 = v - e - 1) : u = v := by omega

/-- If `j = d` then `e + (d - j) = e`. -/
theorem add_sub_eq_of_eq (j d e : ℕ) (hjd : j = d) : e + (d - j) = e := by omega

/-- If `j ≤ d` and `¬ j = d` then `¬ e + (d - j) ≤ e`. -/
theorem sub_gt_of_ne (j d e : ℕ) (hje : j ≤ d) (hjd : ¬ j = d) : ¬ e + (d - j) ≤ e := by omega

/-- The index of the last vertex of the tail of `p` in a concatenation with a nonempty tail. -/
theorem concat_tail_idx (j d e : ℕ) (hje : j ≤ d) (hjd : ¬ j = d) :
    j + 1 + (e + (d - j) - e - 1) = d := by omega

/-- `e < v` implies `0 ≤ v - e - 1`. -/
theorem sub_sub_nonneg (v e : ℕ) (h : e < v) : 0 ≤ v - e - 1 := by omega

/-- **Index bookkeeping for the shortcut, on the first branch.** -/
theorem skip_idx_le (a b d t : ℕ) (hab : a + 2 ≤ b) (hbd : b ≤ d) (ht : t ≤ a) : t < d + 1 := by
  omega

/-- **A `C`-PATH of length `d` from `f i` to `x`.**

`C` is a cycle of `G` carried by the injective map `f : Fin m → V` (`hCmem` says that `C` is exactly
the image of `f`), and `p` is a **simple path of `d` edges** from the vertex `f i` of `C` to the
vertex `x ∉ C`, **none of whose vertices other than `f i` lies on `C`**.

This is the classical *C-path*: the object out of which Mader's structure theorem, and the fan
arguments of Reed–Robertson–Seymour–Thomas, are built. -/
def IsCPath (G : SimpleGraph V) (m d : ℕ) (f : Fin m → V) (i : Fin m) (C : Finset V)
    (_hCmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin m, f j = y) (x : V) (p : Fin (d + 1) → V) : Prop :=
  p ⟨0, zero_lt_d_succ d⟩ = f i
    ∧ p ⟨d, lt_d_succ d⟩ = x
    ∧ x ∉ C
    ∧ Function.Injective p
    ∧ (∀ j : Fin (d + 1), 0 < j.val → p j ∉ C)
    ∧ (∀ j : Fin d,
        G.Adj (p ⟨j.val, Nat.lt_trans j.isLt (lt_d_succ d)⟩)
          (p ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))

variable {f : Fin m → V} {i : Fin m} {C : Finset V}
  {hCmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin m, f j = y} {x : V} {p : Fin (d + 1) → V}

/-- The `C`-path starts at the vertex `f i` of `C`. -/
theorem IsCPath.start (h : IsCPath G m d f i C hCmem x p) : p ⟨0, zero_lt_d_succ d⟩ = f i := h.1

/-- The `C`-path ends at `x`. -/
theorem IsCPath.end (h : IsCPath G m d f i C hCmem x p) : p ⟨d, lt_d_succ d⟩ = x := h.2.1

/-- The target of a `C`-path is **not** on `C`. -/
theorem IsCPath.notMem_end (h : IsCPath G m d f i C hCmem x p) : x ∉ C := h.2.2.1

/-- A `C`-path is a **simple** path. -/
theorem IsCPath.inj (h : IsCPath G m d f i C hCmem x p) : Function.Injective p := h.2.2.2.1

/-- **NO VERTEX OF A `C`-PATH OTHER THAN THE FIRST ONE LIES ON `C`.** -/
theorem IsCPath.notMem_interior (h : IsCPath G m d f i C hCmem x p) (j : Fin (d + 1))
    (hj : 0 < j.val) : p j ∉ C := h.2.2.2.2.1 j hj

/-- **A `C`-path has no interior vertex on `C` at a natural index.** -/
theorem IsCPath.notMem_at (h : IsCPath G m d f i C hCmem x p) (t : ℕ) (ht : t < d + 1) (h0 : 0 < t) :
    p ⟨t, ht⟩ ∉ C := h.2.2.2.2.1 ⟨t, ht⟩ h0

/-- **One step of a `C`-path.** -/
theorem IsCPath.adj (h : IsCPath G m d f i C hCmem x p) (j : Fin d) :
    G.Adj (p ⟨j.val, Nat.lt_trans j.isLt (lt_d_succ d)⟩)
      (p ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :=
  h.2.2.2.2.2 j

/-- Every consecutive pair of vertices of a `C`-path is adjacent, in the form the definition uses. -/
theorem IsCPath.adjAll (h : IsCPath G m d f i C hCmem x p) (j : Fin d) :
    G.Adj (p ⟨j.val, Nat.lt_trans j.isLt (lt_d_succ d)⟩)
      (p ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :=
  h.2.2.2.2.2 j

/-- **One step of a `C`-path, by index.** -/
theorem IsCPath.adj_step (h : IsCPath G m d f i C hCmem x p) (j : ℕ) (hj : j < d) :
    G.Adj (p ⟨j, Nat.lt_trans hj (lt_d_succ d)⟩) (p ⟨j + 1, Nat.succ_lt_succ hj⟩) := by
  simpa using h.adj ⟨j, hj⟩

/-- **The vertex set of a `C`-path.** -/
def IsCPath.supset (p : Fin (d + 1) → V) : Finset V := (Finset.univ : Finset (Fin (d + 1))).image p

theorem IsCPath.mem_supset {p : Fin (d + 1) → V} {y : V} :
    y ∈ IsCPath.supset p ↔ ∃ j : Fin (d + 1), p j = y := by
  simp only [IsCPath.supset, Finset.mem_image]
  constructor
  · rintro ⟨j, -, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, Finset.mem_univ _, rfl⟩

/-- **A `C`-PATH OF LENGTH `d` HAS `d + 1` VERTICES.** -/
theorem IsCPath.card (h : IsCPath G m d f i C hCmem x p) : (IsCPath.supset p).card = d + 1 := by
  rw [IsCPath.supset, Finset.card_image_of_injective _ h.inj]
  simp

/-! ### Part 1 — extending `C`-paths -/

end CPath

/-! The `C`-path shortcuts of Parts 2–3 are in `JSPProblem/CPathSkip.lean`. -/

/-! ### Part 4 — the two-attachment transversal -/

section Attach

/-- **A CYCLE OF LENGTH AT LEAST `3` HAS AN EDGE AVOIDING ANY PRESCRIBED VERTEX OF IT.**

Only the two edges of the cycle through a prescribed vertex meet it, and there are at least three
edges; the proof takes the edge two steps after the prescribed vertex, whose two endpoints cannot
coincide with it because that would force `m ∣ 1` or `m ∣ 2`. -/
theorem IsOddCycle.exists_edge_avoiding {C : Finset V} (hC : IsOddCycle G C)
    {c : V} (hc : c ∈ C) :
    ∃ u v : V, G.Adj u v ∧ u ∈ C ∧ v ∈ C ∧ u ≠ c ∧ v ≠ c := by
  obtain ⟨mm, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  obtain ⟨i₀, hi₀⟩ := (hCmem c).mp hc
  have hdvd1 : ¬ mm ∣ 1 := by
    intro hd
    obtain ⟨c', hc'⟩ := hd
    rcases Nat.eq_zero_or_pos c' with hz | hp
    · rw [hz] at hc'
      omega
    · have hle := Nat.mul_le_mul (le_refl mm) hp
      omega
  have hmod1 : (i₀.val + 1) % mm ≠ i₀.val := by
    intro hh
    have hmod := Nat.mod_add_div (i₀.val + 1) mm
    exact hdvd1 ⟨(i₀.val + 1) / mm, by omega⟩
  have hdvd2 : ¬ mm ∣ 2 := by
    intro hd
    obtain ⟨c', hc'⟩ := hd
    rcases Nat.eq_zero_or_pos c' with hz | hp
    · rw [hz] at hc'
      omega
    · have hle := Nat.mul_le_mul (le_refl mm) hp
      omega
  have hmod2 : (i₀.val + 2) % mm ≠ i₀.val := by
    intro hh
    have hmod := Nat.mod_add_div (i₀.val + 2) mm
    exact hdvd2 ⟨(i₀.val + 2) / mm, by omega⟩
  refine ⟨f ⟨(i₀.val + 1) % mm, Nat.mod_lt _ (Nat.zero_lt_of_lt hm3)⟩,
    f (cycSucc ⟨(i₀.val + 1) % mm, Nat.mod_lt _ (Nat.zero_lt_of_lt hm3)⟩),
    hcyc ⟨(i₀.val + 1) % mm, Nat.mod_lt _ (Nat.zero_lt_of_lt hm3)⟩,
    (hCmem _).mpr ⟨_, rfl⟩, (hCmem _).mpr ⟨_, rfl⟩, ?_, ?_⟩
  · intro he
    have hje : (⟨(i₀.val + 1) % mm, Nat.mod_lt _ (Nat.zero_lt_of_lt hm3)⟩ : Fin mm) = i₀ :=
      hinj (he.trans hi₀.symm)
    exact hmod1 (congrArg Fin.val hje)
  · intro he
    have hje : cycSucc ⟨(i₀.val + 1) % mm, Nat.mod_lt _ (Nat.zero_lt_of_lt hm3)⟩ = i₀ :=
      hinj (he.trans hi₀.symm)
    have hh : ((i₀.val + 1) % mm + 1) % mm = i₀.val := congrArg Fin.val hje
    rw [Nat.mod_add_mod] at hh
    exact hmod2 hh

/-- **THE TWO-ATTACHMENT TRANSVERSAL.**

Let `C` be an **odd cycle** of `G` with `ℓ = |C|` vertices, and suppose **every odd cycle of `G`
meets `C` in at least two vertices**.  Then `G` is the union of a bipartite graph and at most
`ℓ - 1` vertices: delete `C` minus one of its vertices.

No hypothesis of Erdős's kind is used, and the bound `ℓ - 1` does not grow with the packing number —
this is the first transversal bound in this development which is **independent of `k`**. -/
theorem closeToBipartite_of_twoAttach [Fintype V] {C : Finset V} (hC : IsOddCycle G C)
    (hatt : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) :
    CloseToBipartite (C.card - 1) G := by
  have h3 := isOddCycle_card_ge_three hC
  have hpos : 0 < C.card := by omega
  obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp hpos
  have hcard : (C.erase c₀).card ≤ C.card - 1 := by
    rw [Finset.card_erase_of_mem hc₀]
  refine ⟨C.erase c₀, hcard, ?_⟩
  refine isBipartite_delete_of_hitsOddCycles ?_
  intro D hD
  have h2 : 2 ≤ (D ∩ C).card := hatt D hD
  have hle : (({c₀} : Finset V) ∩ (D ∩ C)).card ≤ 1 := by
    calc (({c₀} : Finset V) ∩ (D ∩ C)).card ≤ ({c₀} : Finset V).card :=
          Finset.card_le_card (by
            intro a ha
            exact (Finset.mem_inter.mp ha).1)
      _ = 1 := Finset.card_singleton _
  have hcard_sdiff : ((D ∩ C) \ {c₀}).card
      = (D ∩ C).card - (({c₀} : Finset V) ∩ (D ∩ C)).card := Finset.card_sdiff
  have h1 : 1 ≤ ((D ∩ C) \ {c₀}).card := by
    rw [hcard_sdiff]
    omega
  have hne : (D ∩ C) \ {c₀} ≠ ∅ := by
    intro hz
    rw [hz] at h1
    simp at h1
  have hsub : (D ∩ C) \ {c₀} ⊆ D ∩ (C.erase c₀) := by
    intro a ha
    have ha1 := Finset.mem_sdiff.mp ha
    have haD := Finset.mem_inter.mp ha1.1
    have haC := Finset.mem_inter.mp ha1.1
    refine Finset.mem_inter.mpr ⟨haD.1, Finset.mem_erase.mpr ⟨?_, haC.2⟩⟩
    intro hac
    exact ha1.2 (Finset.mem_singleton.mpr hac)
  intro hdis
  refine hne (Finset.eq_empty_iff_forall_notMem.mpr ?_)
  intro a ha
  rw [Finset.eq_empty_iff_forall_notMem] at hdis
  exact hdis a (hsub ha)

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: THE TWO-ATTACHMENT CLASS.**

If `LocIndep k G` and every odd cycle of `G` meets the odd cycle `C` in at least two vertices, then
`CloseToBipartite (|C| - 1) G` — with a constant **independent of `k`**, against the `ℓ * k` of
`JSPProblem/Transversal.lean` `erdos73On_of_bounded_odd_girth`. -/
theorem erdos73On_of_twoAttach [Fintype V] (k : ℕ) {C : Finset V} (_hG : LocIndep k G)
    (hC : IsOddCycle G C) (hatt : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) :
    CloseToBipartite (C.card - 1) G :=
  closeToBipartite_of_twoAttach hC hatt

end Attach

end

end JSP90
