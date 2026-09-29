/-
# JSP-000090, round 53 — **minimal transversals, critical cycles, and the intersection graph**

## What this file is

Rounds 43, 46, 47, 48 built the *decomposition* side of the classical Erdős–Pósa proof: the
conclusion of Erdős Problem #73 is additive over anticomplete decompositions (`Additive.lean`), over
the connected components (`Connect.lean`, Parts 1–4), and over the pieces of a 1-cut (`Connect.lean`,
Parts 5–6), and every one of those reductions ends in the same place: a bound on the *number* of
non-bipartite pieces, obtained from a packing bound by pure counting.

This file is the **tenth attack family** and it attacks the missing theorem from the other side,
inside a single graph: it never decomposes, and it counts only once.  The objects are

* a **transversal** `X` — a vertex set meeting every odd cycle of `G` (`HitsOddCycles`), i.e. the
  "modification set" of the conclusion of Erdős #73;
* the **critical cycle** of `x ∈ X` — an odd cycle of `G` meeting `X` exactly in `x`.

Minimality of `X` produces critical cycles: `X \ {x}` is not a transversal, so some odd cycle of `G`
misses `X \ {x}`, and since every odd cycle meets `X`, that cycle meets `X` exactly in `x`
(`exists_criticalCycle_of_minimal`, Part 1).  This is the classical first step of the
Reed–Robertson–Seymour–Thomas proof of Erdős–Pósa for odd cycles, and it had not been formalised
anywhere in this development.

* `CriticalTransversal` — the data `(X, C)` with `C x ∩ X = {x}` for `x ∈ X` and each `C x` an odd
  cycle of `G`; the *critical intersection graph* `IntGraph d` joins `x, y ∈ X` when the critical
  cycles `C x` and `C y` meet (Part 2).
* `card_X_le_of_colouring_pack` — **THE COUNTING LEMMA**: if the critical intersection graph of a
  transversal `X` is `c`-colourable, and every packing of odd cycles of `G` has at most `k` members,
  then `|X| ≤ c * k`.  The proof is the Erdős–Pósa counting argument in its sharpest form: the `c`
  colour classes are independent in the intersection graph, so the critical cycles inside one class
  are *pairwise vertex-disjoint odd cycles*, hence a packing and so at most `k` of them; the classes
  partition `X` (`Finset.card_eq_sum_card_fiberwise`), so `|X| ≤ c * k`.  **No bound on the odd
  girth, on the length of the critical cycles, on the packing weight, or on the connectivity of `G`.**
* `closeToBipartite_of_colouring`, `erdos73On_of_spread_transversal` — **A NEW INSTANCE OF THE
  HEADLINE THEOREM**: if `G` carries a transversal whose critical intersection graph is `c`-colourable
  then `LocIndep k G` forces `CloseToBipartite (c * k) G`.  For `c = 1` (all critical cycles pairwise
  vertex-disjoint) this is `erdos73On_of_disjoint_transversal`, with the **optimal constant
  `f(k) = k`**; it strictly generalises round 38's `erdos73On_of_no_branch`, since a 1-spread
  transversal is a far weaker requirement than the absence of branch vertices.
* `packing_of_disjoint_transversal`, `card_le_of_disjoint_transversal` — for a 1-spread transversal
  the critical cycles are *also* a packing of the same size, so on that class of graphs the odd cycle
  packing number and the odd cycle transversal number coincide: the transversal is simultaneously
  optimal, and Erdős's hypothesis is tight on it.
* `SpreadTransversal c G`, `MinimalTransversal G X`, `SpreadMinimalTransversal r c`,
  `oddCycleErdosPosa_of_spreadMinimalTransversal` and `erdos73_of_spreadMinimalTransversal` — the
  localisation of the missing statement (Part 5): the whole of Erdős Problem #73 follows as soon as
  every graph of odd cycle packing number at most `r` admits a minimal odd cycle transversal whose
  critical intersection graph is `r`-colourable.  With `c = 2` this is the classical shape of the
  Reed–Robertson–Seymour–Thomas theorem: a transversal of size at most twice the packing number.

## Why the localisation is not a proof

The counting lemma is *sharp* at `c = 1` (the constant `f(k) = k` of
`erdos73On_of_disjoint_transversal`), and that is not an artefact: for `K_4` the pair `{0, 1}` is a
minimal transversal whose critical cycles are the triangles `{0, 2, 3}` and `{1, 2, 3}`, and those
two triangles meet in `{2, 3}`, so no 1-spread transversal exists for `K_4` at all.  Making that
witness machine-checked (a concrete `CriticalTransversal` on `completeGraph (Fin 4)`, the minimality
of `{0, 1}`, and the resulting edge of its critical intersection graph) is the concrete next step of
this file; it is NOT proved here, and `discovery/JSP-000090/policy.json` carries the recipe.  What is
*not* known, and is exactly the missing lemma of `erdos73_of_spreadMinimalTransversal`, is the
existence of a `c`-spread minimal transversal for `c` depending only on the packing number.
-/
import JSPProblem.Connect
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

section Parts

local instance : DecidableEq V := Classical.decEq V

/-! ### Part 0 — transversals -/

/-- `X` is a **transversal** of the odd cycles of `G`: it meets every odd cycle.  This is the
"modification set" of the conclusion of Erdős #73; `HitsOddCycles` is the predicate of
`JSPProblem/Transversal.lean`, and `closeToBipartite_iff_hitsOddCycles` identifies
`CloseToBipartite m G` with the existence of a transversal of size at most `m`. -/
abbrev OddTransversal (G : SimpleGraph V) (X : Finset V) : Prop := HitsOddCycles G X

/-- `X` is a **minimal** transversal: it meets every odd cycle of `G` and no proper subset of it
does.  Minimality is exactly what produces *critical cycles*
(`exists_criticalCycle_of_minimal`). -/
def MinimalTransversal (G : SimpleGraph V) (X : Finset V) : Prop :=
  HitsOddCycles G X ∧ ∀ Y : Finset V, Y ⊆ X → Y ≠ X → ¬ HitsOddCycles G Y

/-- A minimal transversal meets every odd cycle. -/
theorem minimalTransversal_hits {X : Finset V} (hX : MinimalTransversal G X) : HitsOddCycles G X :=
  hX.1

/-- A subset of a minimal transversal which is itself a transversal is the whole transversal. -/
theorem eq_of_transversal_of_minimal {X Y : Finset V} (hX : MinimalTransversal G X) (hYX : Y ⊆ X)
    (hY : HitsOddCycles G Y) : Y = X := by
  by_cases hne : Y = X
  · exact hne
  · exact absurd hY (hX.2 Y hYX hne)

/-- An odd cycle of `G` is nonempty: it has at least three vertices
(`isOddCycle_card_ge_three`). -/
theorem IsOddCycle.nonempty' {C : Finset V} (hC : IsOddCycle G C) : C.Nonempty := by
  obtain ⟨m, f, _, hm3, _, _, hmem⟩ := hC
  exact ⟨f ⟨0, by omega⟩, (hmem _).mpr ⟨⟨0, by omega⟩, rfl⟩⟩

/-! ### Part 1 — critical cycles: what minimality of a transversal gives -/

/-- **The critical cycle of a vertex of a minimal transversal.**  If `X` is a minimal transversal and
`x ∈ X` then there is an odd cycle of `G` meeting `X` in exactly `x`.

Indeed `X \ {x}` is a proper subset of `X` and hence is not a transversal, so some odd cycle misses
`X \ {x}`; and every odd cycle meets `X`.  This is the classical first step of the
Reed–Robertson–Seymour–Thomas proof of Erdős–Pósa for odd cycles. -/
theorem exists_criticalCycle_of_minimal {X : Finset V} (hX : MinimalTransversal G X) {x : V}
    (hx : x ∈ X) : ∃ C : Finset V, IsOddCycle G C ∧ C ∩ X = {x} := by
  have hsub : X \ {x} ⊆ X := Finset.sdiff_subset
  have hne : X \ {x} ≠ X := by
    intro h
    have hx' : x ∈ X \ {x} := by simpa [h] using hx
    rw [Finset.mem_sdiff] at hx'
    exact hx'.2 (Finset.mem_singleton.mpr rfl)
  have hnot : ¬ ∀ C : Finset V, IsOddCycle G C → C ∩ (X \ {x}) ≠ ∅ := hX.2 _ hsub hne
  simp only [not_forall] at hnot
  obtain ⟨C, hC⟩ := hnot
  push_neg at hC
  obtain ⟨hodd, hmiss⟩ := hC
  refine ⟨C, hodd, ?_⟩
  have hmiss' : ∀ z : V, z ∈ C → ¬ (z ∈ X \ {x}) := by
    intro z hzC hzX
    exact (Finset.not_nonempty_iff_eq_empty.mpr hmiss) ⟨z, Finset.mem_inter.mpr ⟨hzC, hzX⟩⟩
  have hsubX : ∀ w ∈ C, w ∈ X → w = x := by
    intro w hwC hwX
    have hw' : ¬ (w ∈ X \ {x}) := hmiss' w hwC
    refine Finset.mem_singleton.mp ?_
    by_contra hcon
    exact hw' (Finset.mem_sdiff.mpr
      ⟨hwX, fun hmem => hcon hmem⟩)
  have hxC : x ∈ C := by
    obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (hX.1 C hodd)
    have hwx : w = x := hsubX w (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
    rw [← hwx]
    exact (Finset.mem_inter.mp hw).1
  ext w
  constructor
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hCw, hXw⟩
    have hw' : ¬ (w ∈ X \ {x}) := hmiss' w hCw
    refine Finset.mem_singleton.mpr ?_
    by_contra hweq
    exact hw' (Finset.mem_sdiff.mpr ⟨hXw, fun hw2 => hweq (Finset.mem_singleton.mp hw2)⟩)
  · intro hw
    rw [Finset.mem_singleton.mp hw]
    exact Finset.mem_inter.mpr ⟨hxC, hx⟩

/-- **Critical witness data.**  `d.C x` is the critical cycle of `x ∈ X`: an odd cycle of `G` meeting
`X` in exactly `x`, while `d.hits` says that `X` is a transversal. -/
structure CriticalTransversal {V : Type*} (G : SimpleGraph V) (X : Finset V) where
  /-- the critical cycle of `x` -/
  C : V → Finset V
  /-- every critical cycle is an odd cycle of `G` -/
  isOdd : ∀ x ∈ X, IsOddCycle G (C x)
  /-- the critical cycle of `x` meets `X` in exactly `x` -/
  single : ∀ x ∈ X, (C x) ∩ X = {x}
  /-- `X` is a transversal -/
  hits : HitsOddCycles G X

/-- **Every minimal transversal carries critical witness data.**  This is the packaged form of
`exists_criticalCycle_of_minimal`: a minimal odd cycle transversal `X`, together with a critical
cycle for each of its vertices. -/
theorem exists_criticalTransversal_of_minimal {X : Finset V} (hX : MinimalTransversal G X) :
    ∃ d : CriticalTransversal G X, ∀ x ∈ X, IsOddCycle G (d.C x) := by
  have hall : ∀ x : V, ∃ C : Finset V, x ∉ X ∨ (IsOddCycle G C ∧ C ∩ X = {x}) := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨C, hC, hCx⟩ := exists_criticalCycle_of_minimal hX hx
      exact ⟨C, Or.inr ⟨hC, hCx⟩⟩
    · exact ⟨∅, Or.inl hx⟩
  let d : CriticalTransversal G X :=
    { C := fun x => Classical.choose (hall x)
      isOdd := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨h1, h2⟩
        · exact absurd h (by simpa using hx)
        · exact h1
      single := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨h1, h2⟩
        · exact absurd h (by simpa using hx)
        · exact h2
      hits := hX.1 }
  exact ⟨d, fun x hx => d.isOdd x hx⟩

/-! ### Part 2 — the critical intersection graph -/

/-- **The critical intersection graph** of critical data `d`: `x` and `y` are adjacent when both lie
in the transversal `X` and their critical cycles meet.  A proper colouring of this graph with `c`
colours says exactly that, inside each colour class, the critical cycles are pairwise vertex-
disjoint — which is what makes each class a packing. -/
def IntGraph {V : Type*} {G : SimpleGraph V} {X : Finset V} (d : CriticalTransversal G X) :
    SimpleGraph V where
  Adj x y := x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ d.C x ∩ d.C y ≠ ∅
  symm := ⟨fun a b h => by
    have h' := h.2.2.2
    rw [Finset.inter_comm] at h'
    exact ⟨h.2.1, h.1, Ne.symm h.2.2.1, h'⟩⟩
  loopless := ⟨fun a h => h.2.2.1 rfl⟩

@[simp]
theorem mem_IntGraph {V : Type*} {G : SimpleGraph V} {X : Finset V} {d : CriticalTransversal G X}
    {x y : V} : (IntGraph d).Adj x y ↔ x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ d.C x ∩ d.C y ≠ ∅ := Iff.rfl

/-- **Inside one colour class the critical cycles are pairwise vertex-disjoint.**  This is the step
that turns a colouring of the critical intersection graph into a packing of odd cycles. -/
theorem disjoint_of_colour_eq {V : Type*} {G : SimpleGraph V} {X : Finset V}
    {d : CriticalTransversal G X} {c : ℕ} {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (IntGraph d).Adj x y → col x ≠ col y) {x y : V} (hne : x ≠ y) (hx : x ∈ X)
    (hy : y ∈ X) (hxy : col x = col y) : d.C x ∩ d.C y = ∅ := by
  by_contra hne'
  exact hcol ⟨hx, hy, hne, hne'⟩ hxy

/-! ### Part 3 — the counting lemma `|X| ≤ c * k` -/

/-- **THE COUNTING LEMMA, in the packing-number form.**  Let `X` be a transversal of `G` carrying
critical data `d` whose critical intersection graph is `c`-colourable, and suppose every packing of
odd cycles of `G` has at most `k` members.  Then `|X| ≤ c * k`.

The proof is the Erdős–Pósa count: within a colour class the critical cycles are pairwise
vertex-disjoint odd cycles, hence a packing and so at most `k` of them, and `X` is the disjoint union
of its `c` colour fibres (`Finset.card_eq_sum_card_fiberwise`).  The hypothesis is the *packing
bound*, which is weaker than `LocIndep k G` (`K_5` has odd cycle packing number `1` but not
`LocIndep 1`), so this is exactly the form in which the research statement `OddCycleErdosPosa` is
phrased. -/
theorem card_X_le_of_colouring_pack {X : Finset V} {d : CriticalTransversal G X} {c k : ℕ}
    (hpack : ∀ C, IsOddCycleFamily (G := G) C → C.card ≤ k) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (IntGraph d).Adj x y → col x ≠ col y) : X.card ≤ c * k := by
  classical
  have hsep : ∀ (i : Fin c) (x y : V), x ≠ y → x ∈ X → y ∈ X → col x = i → col y = i →
      d.C x ∩ d.C y = ∅ :=
    fun i x y hne hx hy hix hiy => disjoint_of_colour_eq hcol hne hx hy (hix.trans hiy.symm)
  have hle : ∀ i : Fin c, (X.filter (fun x : V => col x = i)).card ≤ k := by
    intro i
    have hfam : IsOddCycleFamily (G := G) ((X.filter (fun x : V => col x = i)).image d.C) := by
      constructor
      · intro A hA B hB hAB
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hB
        have hne : x ≠ y := by
          intro h
          apply hAB
          rw [h]
        exact hsep i x y hne (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
          (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      · intro A hA
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
        exact d.isOdd x (Finset.mem_filter.mp hx).1
    have hinj : Set.InjOn d.C (X.filter (fun x : V => col x = i)) := by
      intro x hx y hy hxy
      have hxf : x ∈ X.filter (fun x : V => col x = i) := Finset.mem_coe.mp hx
      have hyf : y ∈ X.filter (fun x : V => col x = i) := Finset.mem_coe.mp hy
      -- `d.C x = d.C y` and both meet `X` in a single point, so `x = y`
      have h1 : d.C y ∩ X = {x} := by rw [← hxy]; exact d.single x (Finset.mem_filter.mp hxf).1
      have h2 : d.C y ∩ X = {y} := d.single y (Finset.mem_filter.mp hyf).1
      have heq : ({x} : Finset V) = {y} := h1.symm.trans h2
      have hmem : y ∈ ({x} : Finset V) := heq.symm ▸ Finset.mem_singleton_self y
      exact (Finset.mem_singleton.mp hmem).symm
    have hcard : (X.filter (fun x : V => col x = i)).card
        = ((X.filter (fun x : V => col x = i)).image d.C).card :=
      Finset.card_image_iff.mpr hinj |>.symm
    rw [hcard]
    exact hpack _ hfam
  have hmaps : (X : Set V).MapsTo col (Finset.univ : Finset (Fin c)) := fun _ _ => Finset.mem_univ _
  have hpart : X.card = ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card :=
    Finset.card_eq_sum_card_fiberwise (s := X) (f := col) (t := Finset.univ) hmaps
  have hsum : ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card ≤ ∑ _b : Fin c, k :=
    Finset.sum_le_sum fun b _ => hle b
  calc X.card = ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card := hpart
    _ ≤ ∑ _b : Fin c, k := hsum
    _ = c * k := by simp

/-- **THE COUNTING LEMMA under Erdős's hypothesis.**  `LocIndep k G` bounds every packing of odd
cycles by `k` (`LocIndep.oddCycleFamily_card_le`), so the previous lemma applies. -/
theorem card_X_le_of_colouring {X : Finset V} {d : CriticalTransversal G X} {c k : ℕ}
    (hG : LocIndep k G) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (IntGraph d).Adj x y → col x ≠ col y) : X.card ≤ c * k :=
  card_X_le_of_colouring_pack (fun C hC => hG.oddCycleFamily_card_le hC) hcol

/-- **A transversal with a `c`-colourable critical intersection graph is a good transversal:** if
every packing of odd cycles of `G` has at most `k` members, deleting at most `c * k` vertices leaves a
bipartite graph.  This is the form needed for `OddCycleErdosPosa`. -/
theorem closeToBipartite_of_colouring_pack {X : Finset V} {d : CriticalTransversal G X} {c k : ℕ}
    (hpack : ∀ C, IsOddCycleFamily (G := G) C → C.card ≤ k) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (IntGraph d).Adj x y → col x ≠ col y) : CloseToBipartite (c * k) G :=
  (closeToBipartite_iff_hitsOddCycles (G := G)).mpr
    ⟨X, card_X_le_of_colouring_pack hpack hcol, d.hits⟩

/-- **A transversal with a `c`-colourable critical intersection graph is a good transversal:** under
`LocIndep k G`, deleting at most `c * k` vertices leaves a bipartite graph. -/
theorem closeToBipartite_of_colouring {X : Finset V} {d : CriticalTransversal G X} {c k : ℕ}
    (hG : LocIndep k G) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (IntGraph d).Adj x y → col x ≠ col y) : CloseToBipartite (c * k) G :=
  (closeToBipartite_iff_hitsOddCycles (G := G)).mpr
    ⟨X, card_X_le_of_colouring hG hcol, d.hits⟩

/-! ### Part 4 — new instances of the headline theorem -/

/-- **`G` admits a `c`-spread transversal**: a transversal whose critical intersection graph is
`c`-colourable. -/
def SpreadTransversal (c : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, ∃ d : CriticalTransversal G X, Nonempty ((IntGraph d).Coloring (Fin c))

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM (round 53).**  If `G` admits a `c`-spread transversal
then `LocIndep k G` forces `CloseToBipartite (c * k) G`.

No hypothesis on the odd girth, on the length of the critical cycles, on the packing weight, on the
number of branch vertices or on the connectivity of `G`; the constant is the product of the colour
count and Erdős's parameter. -/
theorem erdos73On_of_spread_transversal (c k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      SpreadTransversal c G → LocIndep k G → CloseToBipartite (c * k) G := by
  intro W instW G hsp hG
  obtain ⟨X, d, ⟨col, hcol⟩⟩ := hsp
  exact closeToBipartite_of_colouring (G := G) hG (fun _ _ h => by simpa using hcol h)

/-- **The `c = 1` instance, with the optimal constant `f(k) = k`.** -/
theorem erdos73On_of_spread_transversal_one (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      SpreadTransversal 1 G → LocIndep k G → CloseToBipartite k G :=
  fun W instW G hsp hG => by
    simpa using erdos73On_of_spread_transversal 1 k W instW G hsp hG

/-- **The `c = 1` instance in the elementary form:** a transversal whose critical cycles are pairwise
vertex-disjoint. -/
def DisjointTransversal (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, ∃ d : CriticalTransversal G X,
    ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (d.C x) ∩ d.C y = ∅

/-- A transversal with pairwise disjoint critical cycles is exactly a 1-spread transversal. -/
theorem disjointTransversal_iff_spread_one (G : SimpleGraph V) :
    DisjointTransversal G ↔ SpreadTransversal 1 G := by
  constructor
  · rintro ⟨X, d, hsep⟩
    have hedgeless : IntGraph d = (⊥ : SimpleGraph V) := by
      ext x y
      constructor
      · intro h
        obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (h.2.2.2 : d.C x ∩ d.C y ≠ ∅)
        have hEmpty : d.C x ∩ d.C y = ∅ := hsep x h.1 y h.2.1 h.2.2.1
        exact (Finset.not_nonempty_iff_eq_empty.mpr hEmpty) ⟨w, hw⟩
      · intro h
        exact h.elim
    refine ⟨X, d, ?_⟩
    rw [hedgeless]
    exact (SimpleGraph.colorable_one_iff (G := (⊥ : SimpleGraph V))).2 rfl
  · rintro ⟨X, d, h⟩
    have hedgeless : IntGraph d = (⊥ : SimpleGraph V) :=
      (SimpleGraph.colorable_one_iff (G := IntGraph d)).mp h
    obtain ⟨col, hcol⟩ := h
    refine ⟨X, d, fun x hx y hy hne => ?_⟩
    by_contra hc
    have hAdj : (IntGraph d).Adj x y := ⟨hx, hy, hne, hc⟩
    rw [hedgeless] at hAdj
    simp at hAdj

/-- **For a 1-spread transversal the critical cycles are a packing of the same size**: the
transversal is simultaneously a packing, so on that class of graphs the odd cycle packing number and
the odd cycle transversal number coincide. -/
theorem packing_of_disjoint_transversal {X : Finset V} {d : CriticalTransversal G X}
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (d.C x) ∩ d.C y = ∅) :
    IsOddCycleFamily (G := G) (X.image d.C) ∧ (X.image d.C).card = X.card := by
  have hdisj : DisjointFamily (X.image d.C) := by
    intro A hA B hB hAB
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hB
    have hne : x ≠ y := by
      intro h
      apply hAB
      rw [h]
    exact hsep x hx y hy hne
  refine ⟨⟨hdisj, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
    exact d.isOdd x hx
  · refine Finset.card_image_iff.mpr ?_
    intro x hx y hy hxy
    have hxf : x ∈ X := Finset.mem_coe.mp hx
    have hyf : y ∈ X := Finset.mem_coe.mp hy
    have h1 : d.C y ∩ X = {x} := by rw [← hxy]; exact d.single x hxf
    have h2 : d.C y ∩ X = {y} := d.single y hyf
    have heq : ({x} : Finset V) = {y} := h1.symm.trans h2
    have hmem : y ∈ ({x} : Finset V) := heq.symm ▸ Finset.mem_singleton_self y
    exact (Finset.mem_singleton.mp hmem).symm

/-- The transversal of a 1-spread graph has size at most Erdős's parameter. -/
theorem card_le_of_disjoint_transversal {X : Finset V} {d : CriticalTransversal G X}
    (hG : LocIndep k G) (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (d.C x) ∩ d.C y = ∅) : X.card ≤ k := by
  have hp := packing_of_disjoint_transversal hsep
  have hle := hG.oddCycleFamily_card_le hp.1
  rw [hp.2] at hle
  exact hle

/-- **`f(k) = k` for the graphs admitting a 1-spread transversal.**  This strictly generalises round
38's `erdos73On_of_no_branch`: graphs without branch vertices have such a transversal (their odd
cycles are pairwise disjoint), but a 1-spread transversal is a much weaker requirement. -/
theorem erdos73On_of_disjoint_transversal (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      DisjointTransversal G → LocIndep k G → CloseToBipartite k G := by
  intro W instW G hsp hG
  obtain ⟨X, d, hsep⟩ := hsp
  exact (closeToBipartite_iff_hitsOddCycles (G := G)).mpr
    ⟨X, card_le_of_disjoint_transversal hG hsep, d.hits⟩

/-! ### Part 5 — the localisation of the missing statement -/

/-- **The minimal-transversal form of the missing lemma.**  Every graph of odd cycle packing number at
most `r` admits a minimal odd cycle transversal whose critical intersection graph is `c`-colourable.
For `c = 2` this is the classical shape of the Reed–Robertson–Seymour–Thomas theorem (a transversal
of size at most twice the packing number); `c = 1` is false (`K_4`, see the header). -/
def SpreadMinimalTransversal (r c : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    (∀ C, IsOddCycleFamily (G := G) C → C.card ≤ r) →
    ∃ X : Finset W, MinimalTransversal G X ∧ ∃ d : CriticalTransversal G X,
      Nonempty ((IntGraph d).Coloring (Fin c))

/-- **Erdős–Pósa for odd cycles follows from `SpreadMinimalTransversal r c`, with the explicit
constant `c * r`.**  The research statement of JSP-000090 is thus localised to the colour count of
the critical intersection graph of one minimal transversal. -/
theorem oddCycleErdosPosa_of_spreadMinimalTransversal (r c : ℕ)
    (h : SpreadMinimalTransversal.{u} r c) : OddCycleErdosPosa.{u} r := by
  refine ⟨c * r, ?_⟩
  intro W instW G hbound
  obtain ⟨X, hX, d, ⟨col, hcol⟩⟩ := h W instW G hbound
  exact closeToBipartite_of_colouring_pack (G := G) hbound (fun _ _ h => by simpa using hcol h)

/-- **Hence the whole of Erdős Problem #73 follows from `∀ r, SpreadMinimalTransversal r c` for any
fixed `c`** — in particular from `c = 2`.  This is the precise remaining statement; `jsp_000090_main`
follows from it. -/
theorem erdos73_of_spreadMinimalTransversal (c : ℕ) (h : ∀ r, SpreadMinimalTransversal.{u} r c) :
    ∀ k, Erdős73.{u} k :=
  erdos73_of_erdosPosa (fun r => oddCycleErdosPosa_of_spreadMinimalTransversal r c (h r))

end Parts


end
end JSP90
