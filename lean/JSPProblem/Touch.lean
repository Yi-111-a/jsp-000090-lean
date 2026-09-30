import JSPProblem.Double

/-!
# JSP-000090, round 74 — the **touching axis**: the odd cycles that reach the boundary from outside,
# and the minimal transversal of the *touching* family

This is the **twenty-third attack family**.  It is aimed at the concrete next lemma named in
`discovery/JSP-000090/policy.json` after rounds 72 and 73 — bound the chromatic number of the fan
critical intersection graph — and at the *secondary* lemma those rounds recorded as **unsolved**:
the **touching property**, i.e. the fact that a minimal transversal of the odd cycles *contained*
in `∂C` need not meet an odd cycle that merely *touches* `∂C`.  Round 73 therefore had to state it
as a second, explicit conjunct of `JSP90.FanCriticalErdős73`, "not automatic".

## What is proved

### Part 1 — the touching family and its minimal transversals

`Touches`, `HitsTouching`, `MinTouching`, and

* **`JSP90.exists_criticalTouchCycle_of_minimal`** — for every vertex `x` of a *minimal transversal
  of the touching odd cycles* there is an odd cycle `D` which **touches** `∂C` and meets `X` in
  exactly `x`;
* **`JSP90.minTouching_hits`** — such a transversal **meets every odd cycle meeting `∂C`, by
  definition**.

So round 73's second conjunct is discharged *by construction*: the touching property is no longer
something to be proved of a minimal transversal of the contained cycles, it is the definition of
the family being hit.  What is paid for it is that the critical cycles are no longer known to lie
in `∂C`, so (i) the packing bound available in the counting lemma is `k` rather than round 73's
`k − 1`, and (ii) the cell structure of `JSPProblem/Double.lean` does not apply to them.  The
converse direction is recorded as a theorem,
`JSP90.TouchCriticalErdős73.of_fanCritical`.

### Part 2 — the critical intersection graph of the touching family, and the counting

`TouchInt`, `TouchIntGraph`, `touchDisjoint_of_colour_eq`, `card_critTransversal_le_of_colouring_pack`,
`card_touchTransversal_le_of_colouring_pack`, `card_touchTransversal_le_of_colouring`
(`|X| ≤ c · k`), `card_touchTransversal_le_one`.

### Part 3 — the remaining statement, with ONE conjunct instead of two

`JSP90.TouchCriticalErdős73 c`, `JSP90.fanErdős73_of_touchCritical`,
`JSP90.erdos73On_of_touchCritical`, **`JSP90.erdos73_of_touchCritical`**,
`JSP90.TouchCriticalErdős73.of_fanCritical`.

### Part 4 — a NEW instance of the headline theorem on the **DEGREE AXIS**

`LocalDegreeOutside`, `hitsOddCycles_of_localDegreeOutside`,
`closeToBipartite_of_localDegreeOutside` and **`erdos73On_of_localDegreeOutside`**, whose constant
is `m`: if at most `m` vertices carry all the "interior" degree (every vertex outside them has at
most **one** neighbour outside them), then those `m` vertices meet *every* odd cycle, so `G` is
`m`-close to bipartite.  This beats `JSP90.erdos73On_of_bounded_branch`'s `m + k` on this class, and
assumes no bound on the odd girth, on the packing number, on the packing weight, or on the number
of branch vertices.

## What is *not* proved

`JSP90.TouchCriticalErdős73 c` for some `c` — i.e. that the critical intersection graph of a
minimal transversal of the touching odd cycles has **bounded chromatic number in terms of `k`
alone**.  Behind it stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas, JCTA-B
2003).  No colouring bound is claimed or assumed anywhere.
-/

namespace JSP90

open Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance : DecidableEq V := Classical.decEq V

/-! ## Part 1 — the touching family -/

section Touching

/-- **The odd cycle `D` TOUCHES the boundary of `C`**: it has a vertex at distance exactly one
from `C`.  This is the family `JSP90.FanErdős73` asks a transversal of. -/
noncomputable def Touches (G : SimpleGraph V) (C D : Finset V) : Prop :=
  D ∩ boundary G C ≠ ∅

theorem mem_touches {C D : Finset V} {x : V} (hD : x ∈ D) (hC : x ∈ boundary G C) :
    Touches G C D :=
  ne_inter_of_mem hD hC

/-- **`X` HITS EVERY TOUCHING ODD CYCLE** — the property `JSP90.FanErdős73` asks of its set `Z`. -/
noncomputable def HitsTouching (G : SimpleGraph V) (C X : Finset V) : Prop :=
  ∀ D : Finset V, IsOddCycle G D → Touches G C D → D ∩ X ≠ ∅

/-- **A MINIMAL TRANSVERSAL OF THE TOUCHING ODD CYCLES.**  Minimality is with respect to the
touching family, so the critical cycles produced from it are touching cycles. -/
noncomputable def MinTouching (G : SimpleGraph V) (C X : Finset V) : Prop :=
  HitsTouching G C X ∧ ∀ Y : Finset V, Y ⊆ X → Y ≠ X → ¬ HitsTouching G C Y

/-- **A minimal transversal of the touching family meets every odd cycle meeting `∂C`, by
definition.**  This is round 73's second conjunct, discharged. -/
theorem minTouching_hits {X : Finset V} (hX : MinTouching G C X) : HitsTouching G C X :=
  hX.1

theorem eq_of_touchTransversal_of_minimal {X Y : Finset V} (hX : MinTouching G C X)
    (hYX : Y ⊆ X) (hY : HitsTouching G C Y) : Y = X := by
  by_cases hne : Y = X
  · exact hne
  · exact absurd hY (hX.2 Y hYX hne)

/-- **THE BOUNDARY OF `C` IS A TRANSVERSAL OF THE TOUCHING ODD CYCLES** — trivially, but it is
the anchor that makes `JSP90.exists_minTouching` go through. -/
theorem hitsTouching_boundary {C : Finset V} : HitsTouching G C (boundary G C) := by
  intro D _hD hDb
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hDb
  exact ne_inter_of_mem (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2

/-- **A MINIMAL TRANSVERSAL OF THE TOUCHING ODD CYCLES EXISTS INSIDE ANY GIVEN TRANSVERSAL**, by
the finitary argument `JSP90.exists_minTouching_of_transversal`. -/
theorem exists_minTouching_of_transversal (X₀ : Finset V) (hX₀ : HitsTouching G C X₀) :
    ∃ X : Finset V, X ⊆ X₀ ∧ MinTouching G C X := by
  classical
  have hsne : ((Finset.univ : Finset (Finset V)).filter
      (fun Y : Finset V => Y ⊆ X₀ ∧ HitsTouching G C Y)).Nonempty := by
    refine Finset.filter_nonempty_iff.mpr
      ⟨X₀, Finset.mem_univ _, Finset.Subset.refl _, hX₀⟩
  obtain ⟨X, hXs, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset V)).filter
      (fun Y : Finset V => Y ⊆ X₀ ∧ HitsTouching G C Y)) Finset.card hsne
  rw [Finset.mem_filter] at hXs
  obtain ⟨hXsub, hX⟩ := hXs.2
  refine ⟨X, hXsub, hX, fun Y hYX hne hY => ?_⟩
  have hmem : (Y : Finset V)
      ∈ (Finset.univ : Finset (Finset V)).filter
          (fun Z : Finset V => Z ⊆ X₀ ∧ HitsTouching G C Z) := by
    have hsub2 : Y ⊆ X₀ := fun a ha => hXsub (hYX ha)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsub2, hY⟩
  have hlt : Y.card < X.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hYX, hne⟩)
  exact absurd hlt (Nat.not_lt.mpr (hmin Y hmem))

/-- **A MINIMAL TRANSVERSAL OF THE TOUCHING ODD CYCLES EXISTS.** -/
theorem exists_minTouching {C : Finset V} : ∃ X : Finset V, MinTouching G C X := by
  obtain ⟨X, -, hX⟩ :=
    exists_minTouching_of_transversal (X₀ := boundary G C) (hitsTouching_boundary (C := C))
  exact ⟨X, hX⟩

/-- **THE CRITICAL CYCLE OF A VERTEX OF A MINIMAL TRANSVERSAL OF THE TOUCHING FAMILY TOUCHES THE
BOUNDARY.**

This is the statement round 73 could not make: `JSP90.exists_criticalFanCycle_of_minimal` produces
a critical cycle *contained in* `∂C` (from a minimal transversal of the contained family), while
this produces a critical cycle that *touches* `∂C` (from a minimal transversal of the touching
family).  Minimality of `X` says `X \ {x}` is not a transversal of the touching family, so some
touching odd cycle misses it. -/
theorem exists_criticalTouchCycle_of_minimal {X : Finset V} (hX : MinTouching G C X) {x : V}
    (hx : x ∈ X) :
    ∃ D : Finset V, IsOddCycle G D ∧ Touches G C D ∧ D ∩ X = {x} := by
  have hsub : X \ {x} ⊆ X := Finset.sdiff_subset
  have hne : X \ {x} ≠ X := by
    intro h
    have hx' : x ∈ X \ {x} := by simpa [h] using hx
    rw [Finset.mem_sdiff] at hx'
    exact hx'.2 (Finset.mem_singleton.mpr rfl)
  have hnot : ¬ HitsTouching G C (X \ {x}) := hX.2 _ hsub hne
  simp only [HitsTouching, not_forall] at hnot
  obtain ⟨D, hD⟩ := hnot
  push Not at hD
  obtain ⟨hodd, htouch, hmiss⟩ := hD
  refine ⟨D, hodd, htouch, ?_⟩
  have hmiss' : ∀ z : V, z ∈ D → ¬ (z ∈ X \ {x}) := by
    intro z hzD hzX
    exact (Finset.not_nonempty_iff_eq_empty.mpr hmiss) ⟨z, Finset.mem_inter.mpr ⟨hzD, hzX⟩⟩
  have hsubX : ∀ w ∈ D, w ∈ X → w = x := by
    intro w hwD hwX
    have hw' : ¬ (w ∈ X \ {x}) := hmiss' w hwD
    refine Finset.mem_singleton.mp ?_
    by_contra hcon
    exact hw' (Finset.mem_sdiff.mpr ⟨hwX, fun hmem => hcon hmem⟩)
  have hxD : x ∈ D := by
    obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (hX.1 D hodd htouch)
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
    exact Finset.mem_inter.mpr ⟨hxD, hx⟩

/-- **CRITICAL WITNESS DATA FOR THE TOUCHING FAMILY.**  `d.crit x` is the critical cycle of
`x ∈ X`: an odd cycle of `G` *touching* `∂C` and meeting `X` in exactly `x`; `d.hits` says `X` meets
every odd cycle touching `∂C`.  The `touch` field is what the fan statement consumes. -/
structure TouchCritical {V : Type*} [Fintype V] (G : SimpleGraph V) (C X : Finset V) where
  /-- the critical cycle of `x` -/
  crit : V → Finset V
  /-- every critical cycle is an odd cycle of `G` -/
  isOdd : ∀ x ∈ X, IsOddCycle G (crit x)
  /-- **every critical cycle TOUCHES `∂C`** — the new content with respect to round 53 -/
  touch : ∀ x ∈ X, Touches G C (crit x)
  /-- the critical cycle of `x` meets `X` in exactly `x` -/
  single : ∀ x ∈ X, (crit x) ∩ X = {x}
  /-- `X` meets every odd cycle touching `∂C` -/
  hits : HitsTouching G C X

/-- **EVERY MINIMAL TRANSVERSAL OF THE TOUCHING FAMILY CARRIES CRITICAL WITNESS DATA.** -/
theorem exists_criticalTouchTransversal_of_minimal {X : Finset V} (hX : MinTouching G C X) :
    ∃ d : TouchCritical G C X, ∀ x ∈ X, IsOddCycle G (d.crit x) ∧ Touches G C (d.crit x) := by
  have hall : ∀ x : V, ∃ D : Finset V, x ∉ X ∨
      (IsOddCycle G D ∧ Touches G C D ∧ D ∩ X = {x}) := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨D, hD, htouch, hDx⟩ := exists_criticalTouchCycle_of_minimal hX hx
      exact ⟨D, Or.inr ⟨hD, htouch, hDx⟩⟩
    · exact ⟨∅, Or.inl hx⟩
  let d : TouchCritical G C X :=
    { crit := fun x => Classical.choose (hall x)
      isOdd := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨h1, _, _⟩
        · exact absurd h (by simpa using hx)
        · exact h1
      touch := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨_, h2, _⟩
        · exact absurd h (by simpa using hx)
        · exact h2
      single := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨_, _, h3⟩
        · exact absurd h (by simpa using hx)
        · exact h3
      hits := hX.1 }
  exact ⟨d, fun x hx => ⟨d.isOdd x hx, d.touch x hx⟩⟩

end Touching

/-! ## Part 2 — the critical intersection graph of the touching family, and the counting -/

section TouchInt

/-- **THE CRITICAL INTERSECTION GRAPH**, for an arbitrary set of critical cycles `crit` and a
transversal `X`: `x` and `y` are adjacent when both lie in `X`, are distinct, and their critical
cycles meet.  It is stated without the data structure so that the same graph serves the touching
family (Part 1) and round 73's fan family. -/
def TouchInt (X : Finset V) (crit : V → Finset V) : SimpleGraph V where
  Adj x y := x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ crit x ∩ crit y ≠ ∅
  symm := ⟨fun a b h => by
    have h' := h.2.2.2
    rw [Finset.inter_comm] at h'
    exact ⟨h.2.1, h.1, Ne.symm h.2.2.1, h'⟩⟩
  loopless := ⟨fun a h => h.2.2.1 rfl⟩

@[simp]
theorem mem_TouchInt {V : Type*} [Fintype V] {X : Finset V} {crit : V → Finset V} {x y : V} :
    (TouchInt X crit).Adj x y ↔ x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ crit x ∩ crit y ≠ ∅ := Iff.rfl

/-- **THE CRITICAL INTERSECTION GRAPH OF THE TOUCHING FAMILY.** -/
noncomputable def TouchIntGraph {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    (d : TouchCritical G C X) : SimpleGraph V :=
  TouchInt X d.crit

@[simp]
theorem mem_TouchIntGraph {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    {d : TouchCritical G C X} {x y : V} :
    (TouchIntGraph d).Adj x y ↔ x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ d.crit x ∩ d.crit y ≠ ∅ := Iff.rfl

/-- **INSIDE ONE COLOUR CLASS THE CRITICAL CYCLES ARE PAIRWISE VERTEX-DISJOINT.** -/
theorem touchDisjoint_of_colour_eq {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    {d : TouchCritical G C X} {c : ℕ} {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (TouchIntGraph d).Adj x y → col x ≠ col y) {x y : V} (hne : x ≠ y)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : col x = col y) : d.crit x ∩ d.crit y = ∅ := by
  by_contra hne'
  exact hcol ⟨hx, hy, hne, hne'⟩ hxy

/-- **THE COUNTING LEMMA, IN ITS GENERAL FORM: `|X| ≤ c * r`.**

`X` is a set carrying *critical cycles* `crit` (odd cycles meeting `X` in exactly one point),
`hpack` bounds every packing of odd cycles of `G` by `r`, and `hcol` is a proper `c`-colouring of
the critical intersection graph.  Inside each colour class the critical cycles are pairwise
vertex-disjoint, hence a packing, hence at most `r` of them.

The form is separated from the data structure so that it can be used both for the touching family
and for round 73's fan family. -/
theorem card_critTransversal_le_of_colouring_pack {X : Finset V} {crit : V → Finset V} {c r : ℕ}
    (hisOdd : ∀ x ∈ X, IsOddCycle G (crit x))
    (hsingle : ∀ x ∈ X, (crit x) ∩ X = {x})
    (hpack : ∀ 𝒟, IsOddCycleFamily (G := G) 𝒟 → 𝒟.card ≤ r) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, x ∈ X → y ∈ X → x ≠ y → (crit x) ∩ (crit y) ≠ ∅ → col x ≠ col y) :
    X.card ≤ c * r := by
  classical
  have hsep : ∀ (i : Fin c) (x y : V), x ≠ y → x ∈ X → y ∈ X → col x = i → col y = i →
      crit x ∩ crit y = ∅ :=
    fun i x y hne hx hy hix hiy => by
      by_contra hcon
      exact hcol hx hy hne hcon (hix.trans hiy.symm)
  have hle : ∀ i : Fin c, (X.filter (fun x : V => col x = i)).card ≤ r := by
    intro i
    have hfam : IsOddCycleFamily (G := G) ((X.filter (fun x : V => col x = i)).image crit) := by
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
        exact hisOdd x (Finset.mem_filter.mp hx).1
    have hinj : Set.InjOn crit (X.filter (fun x : V => col x = i)) := by
      intro x hx y hy hxy
      have hxf : x ∈ X.filter (fun x : V => col x = i) := Finset.mem_coe.mp hx
      have hyf : y ∈ X.filter (fun x : V => col x = i) := Finset.mem_coe.mp hy
      have h1 : crit y ∩ X = {x} := by
        rw [← hxy]
        exact hsingle x (Finset.mem_filter.mp hxf).1
      have h2 : crit y ∩ X = {y} := hsingle y (Finset.mem_filter.mp hyf).1
      have heq : ({x} : Finset V) = {y} := h1.symm.trans h2
      have hmem : y ∈ ({x} : Finset V) := heq.symm ▸ Finset.mem_singleton_self y
      exact (Finset.mem_singleton.mp hmem).symm
    have hcard : (X.filter (fun x : V => col x = i)).card
        = ((X.filter (fun x : V => col x = i)).image crit).card :=
      Finset.card_image_iff.mpr hinj |>.symm
    rw [hcard]
    exact hpack _ hfam
  have hmaps : (X : Set V).MapsTo col (Finset.univ : Finset (Fin c)) :=
    fun _ _ => Finset.mem_univ _
  have hpart : X.card = ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card :=
    Finset.card_eq_sum_card_fiberwise (s := X) (f := col) (t := Finset.univ) hmaps
  have hsum : ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card ≤ ∑ _b : Fin c, r :=
    Finset.sum_le_sum fun b _ => hle b
  calc X.card = ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card := hpart
    _ ≤ ∑ _b : Fin c, r := hsum
    _ = c * r := by simp

/-- **THE COUNTING LEMMA FOR THE TOUCHING FAMILY, IN THE PACKING-BOUND FORM: `|X| ≤ c * r`.**

`hpack` is a bound on the size of *every* packing of odd cycles of `G` — not only of the ones
contained in `∂C`, because the critical cycles of a minimal transversal of the touching family are
only known to touch `∂C`.  That is exactly the price paid for the touching property, and it is
where round 73's `k − 1` degrades to `k`. -/
theorem card_touchTransversal_le_of_colouring_pack {X : Finset V} {d : TouchCritical G C X}
    {c r : ℕ} (hpack : ∀ 𝒟, IsOddCycleFamily (G := G) 𝒟 → 𝒟.card ≤ r) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (TouchIntGraph d).Adj x y → col x ≠ col y) : X.card ≤ c * r :=
  card_critTransversal_le_of_colouring_pack d.isOdd d.single hpack (col := col)
    (fun _ _ hx hy hne hinter => hcol ⟨hx, hy, hne, hinter⟩)

/-- **THE COUNTING LEMMA FOR THE TOUCHING FAMILY UNDER ERDŐS'S HYPOTHESIS: `|X| ≤ c * k`.** -/
theorem card_touchTransversal_le_of_colouring {X : Finset V} {d : TouchCritical G C X}
    {c k : ℕ} (hG : LocIndep k G) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (TouchIntGraph d).Adj x y → col x ≠ col y) : X.card ≤ c * k :=
  card_touchTransversal_le_of_colouring_pack (fun C hC => hG.oddCycleFamily_card_le hC) hcol

/-- **THE `c = 1` SHAPE: A MINIMAL TRANSVERSAL OF THE TOUCHING FAMILY WHOSE CRITICAL CYCLES ARE
PAIRWISE VERTEX-DISJOINT HAS `|X| ≤ k`.** -/
theorem card_touchTransversal_le_one (hG : LocIndep k G) {X : Finset V}
    {d : TouchCritical G C X}
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (d.crit x) ∩ (d.crit y) = ∅) : X.card ≤ k := by
  have hcol : ∀ ⦃x y : V⦄, (TouchIntGraph d).Adj x y → (0 : Fin 1) ≠ (0 : Fin 1) := by
    intro x y hxy
    obtain ⟨hx, hy, hne, hinter⟩ := hxy
    exact absurd (hsep x hx y hy hne) hinter
  simpa using card_touchTransversal_le_of_colouring hG (c := 1) (col := fun _ => (0 : Fin 1)) hcol

end TouchInt

/-! ## Part 3 — the remaining statement, with ONE conjunct instead of two -/

section TouchCritical

/-- **THE GRAPH `H` IS `c`-COLOURABLE**, written as a `Prop` so that it can be read off the
critical intersection graph without unpacking a `SimpleGraph.Coloring`. -/
noncomputable def TouchColourable {V : Type*} [Fintype V] (H : SimpleGraph V) (c : ℕ) : Prop :=
  ∃ col : V → Fin c, ∀ ⦃x y : V⦄, H.Adj x y → col x ≠ col y

/-- **THE CRITICAL-CYCLE HYPOTHESIS AT THE FAN, WITH A SINGLE CONJUNCT.**

For every triangle-free `G` with `LocIndep k G`, every odd cycle `C`, and every `c`, there is a
minimal transversal `X` of the odd cycles **touching** `∂C`, with critical data `d`, such that

* every critical cycle of `d` is an odd cycle of `G` touching `∂C`;
* **the critical intersection graph of `d` is `c`-colourable** — the content, and with
  `JSP90.card_touchTransversal_le_of_colouring` it forces `|X| ≤ c * k`;
* `|X| ≤ c * k` outright (this is the conjunct the reduction consumes).

This is the remaining statement of JSP-000090 on the touching axis.  It replaces round 73's
`JSP90.FanCriticalErdős73 c`, which had **two** conjuncts — a colouring of a minimal transversal of
the *contained* cycles **and** the touching property, the latter being explicitly *not* automatic.
Here the touching property has been built into the definition of the family, and the packing bound
has degraded from `k − 1` to `k`. -/
noncomputable def TouchCriticalErdős73 (c : ℕ) : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
    ∀ C : Finset W, IsOddCycle G C →
      ∃ (X : Finset W) (d : TouchCritical G C X),
        (∀ x ∈ X, IsOddCycle G (d.crit x) ∧ Touches G C (d.crit x))
        ∧ TouchColourable (TouchIntGraph d) c
        ∧ X.card ≤ c * k

/-- **THE FAN STATEMENT WITH THE EXPLICIT CONSTANT `c * k`, FROM THE TOUCHING CRITICAL-CYCLE
HYPOTHESIS.**  The size bound is the last conjunct, and the touching property is `d.hits`. -/
theorem fanErdős73_of_touchCritical {c : ℕ} (h : TouchCriticalErdős73.{u} c) :
    FanErdős73.{u} (fun k => c * k) := by
  intro k W instW G hG hG3 C hC
  obtain ⟨X, d, _, _, hcard⟩ := h k W instW G hG hG3 C hC
  refine ⟨X, hcard, fun D hD hDb => ?_⟩
  have hne : (D ∩ X).Nonempty := Finset.nonempty_iff_ne_empty.mpr (d.hits D hD hDb)
  obtain ⟨x, hx⟩ := hne
  exact Finset.ne_empty_of_mem hx

/-- **ERDŐS PROBLEM #73, WITH THE EXPLICIT CONSTANT `fanBound (fun _ => c * k) k`, FROM THE
TOUCHING CRITICAL-CYCLE HYPOTHESIS.** -/
theorem erdos73On_of_touchCritical {c : ℕ} (h : TouchCriticalErdős73.{u} c) (k : ℕ) :
    Erdős73On.{u} k (fanBound (fun j => c * j) k) := by
  show ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
    CloseToBipartite (fanBound (fun j => c * j) k) G
  exact erdos73On_of_fanErdős73 (f := fun j => c * j) (fanErdős73_of_touchCritical h) k

/-- **ERDŐS PROBLEM #73 IN FULL FROM THE TOUCHING CRITICAL-CYCLE HYPOTHESIS.** -/
theorem erdos73_of_touchCritical {c : ℕ} (h : TouchCriticalErdős73.{u} c) :
    ∀ k, Erdős73.{u} k :=
  erdos73_of_fanErdős73 (fanErdős73_of_touchCritical h)

/-- **ROUND 73's HYPOTHESIS IMPLIES THIS ROUND'S.**  A minimal transversal of the *contained* odd
cycles which additionally meets every *touching* odd cycle is, in particular, a transversal of the
touching family; a minimal transversal of the touching family inside it is at least as small, and
round 73's counting `JSP90.card_fanTransversal_le_of_colouring` gives `|X| ≤ c * (k − 1) ≤ c * k`.

This records that the statement proved necessary this round is a consequence of the one named in
`discovery/JSP-000090/policy.json` before it: the two are the **same missing lemma**, and round 73's
extra "touching" conjunct was an artefact of choosing the wrong family of odd cycles. -/
theorem TouchCriticalErdős73.of_fanCritical {c : ℕ} (h : FanCriticalErdős73.{u} c) :
    TouchCriticalErdős73.{u} c := by
  intro k W instW G hG hG3 C hC
  obtain ⟨X, hX, d, ⟨col, hcol⟩, htouch⟩ := h k W instW G hG hG3 C hC
  have hcol0 : ∀ ⦃x y : W⦄, (FanIntGraph d).Adj x y → col x ≠ col y := fun _ _ hxy => by
    simpa using hcol hxy
  have hcard : X.card ≤ c * k := by
    refine Nat.le_trans (card_fanTransversal_le_of_colouring hG hC (d := d) (c := c) (col := col)
      hcol0) ?_
    exact Nat.mul_le_mul_left c (Nat.sub_le _ _)
  have hXtouch : HitsTouching G C X := fun D hD hDb => htouch D hD hDb
  obtain ⟨X', hX', hmin⟩ := exists_minTouching_of_transversal (X₀ := X) hXtouch
  have hhit : HitsTouching G C X' := fun D hD hDb => hmin.1 D hD hDb
  let dt : TouchCritical G C X' :=
    { crit := d.crit
      isOdd := fun x hx => d.isOdd x (hX' hx)
      touch := fun x hx => by
        have hne : (d.crit x).Nonempty := (d.isOdd x (hX' hx)).nonempty
        obtain ⟨y, hy⟩ := hne
        exact mem_touches hy (d.subBoundary x (hX' hx) hy)
      single := fun x hx => by
        have hone : d.crit x ∩ X = {x} := d.single x (hX' hx)
        have hmemx : x ∈ d.crit x ∧ x ∈ X :=
          Finset.mem_inter.mp (hone ▸ Finset.mem_singleton_self x)
        have h1 : d.crit x ∩ X' ⊆ d.crit x ∩ X := by
          intro y hy
          have hy' := Finset.mem_inter.mp hy
          have hyx : y ∈ d.crit x ∧ y ∈ X := by
            exact ⟨hy'.1, hX' hy'.2⟩
          exact Finset.mem_inter.mpr hyx
        rw [hone] at h1
        have hxX : x ∈ d.crit x ∩ X' := by
          have hxx : x ∈ d.crit x ∧ x ∈ X' := by
            exact ⟨hmemx.1, hx⟩
          exact Finset.mem_inter.mpr hxx
        exact Finset.Subset.antisymm h1 (Finset.singleton_subset_iff.mpr hxX)
      hits := hhit }
  have hcrit : ∀ x ∈ X', IsOddCycle G (dt.crit x) ∧ Touches G C (dt.crit x) :=
    fun x hx => by
      refine ⟨d.isOdd x (hX' hx), ?_⟩
      have hne : (d.crit x).Nonempty := (d.isOdd x (hX' hx)).nonempty
      obtain ⟨y, hy⟩ := hne
      exact mem_touches hy (d.subBoundary x (hX' hx) hy)
  have hcol' : TouchColourable (TouchIntGraph dt) c := by
    refine ⟨col, ?_⟩
    intro x y hxy
    obtain ⟨hx, hy, hne, hinter⟩ := hxy
    exact hcol0 (mem_FanIntGraph.mpr ⟨hX' hx, hX' hy, hne, hinter⟩)
  refine ⟨X', dt, hcrit, hcol', ?_⟩
  exact Nat.le_trans (Finset.card_le_card hX') hcard

end TouchCritical

/-! ## Part 4 — a NEW instance of the headline theorem on the **DEGREE AXIS** -/

section Degree

/-- **`G` IS EDGELESS OUTSIDE A SET OF AT MOST `m` VERTICES**: there is `H` with `|H| ≤ m` and no
edge of `G` with both ends outside `H`.  Equivalently, `G` is a subgraph of the join of `G[H]`
with an edgeless graph on `V \ H`.

This is a hypothesis about the **degree distribution** of `G` alone.  No bound is assumed on the
odd girth, on the packing number, on the packing weight, or on the number of branch vertices. -/
noncomputable def EdgelessOutside (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ H : Finset V, H.card ≤ m ∧ ∀ v w : V, v ∉ H → w ∉ H → ¬ G.Adj v w

/-- **EVERY ODD CYCLE OF `G` MEETS `H`**: an odd cycle carries an edge, and no edge of `G` has both
ends outside `H`. -/
theorem hitsOddCycles_of_edgelessOutside {H : Finset V} (hH : H.card ≤ m)
    (hedgeless : ∀ v w : V, v ∉ H → w ∉ H → ¬ G.Adj v w) : HitsOddCycles G H := by
  intro D hD
  obtain ⟨n, f, _, hn3, _, hcyc, hmem⟩ := hD
  have h0 : Fin n := ⟨0, by omega⟩
  have hf0D : f h0 ∈ D := (hmem _).mpr ⟨h0, rfl⟩
  have hf1D : f (cycSucc h0) ∈ D := (hmem _).mpr ⟨cycSucc h0, rfl⟩
  by_cases hmem0 : f h0 ∈ H
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hf0D, hmem0⟩)
  by_cases hmem1 : f (cycSucc h0) ∈ H
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hf1D, hmem1⟩)
  · exact absurd (hcyc h0) (hedgeless (f h0) (f (cycSucc h0)) hmem0 hmem1)


/-- **`H` IS AN ODD CYCLE TRANSVERSAL OF `G`, SO `G` IS `|H|`-CLOSE TO BIPARTITE.** -/
theorem closeToBipartite_of_edgelessOutside {m : ℕ} (h : EdgelessOutside G m) :
    CloseToBipartite m G := by
  obtain ⟨H, hH, hedgeless⟩ := h
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mpr
    ⟨H, hH, hitsOddCycles_of_edgelessOutside hH hedgeless⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM ON THE DEGREE AXIS:**
`LocIndep k G → EdgelessOutside m G → CloseToBipartite m G`.

The constant is `m` and does not involve `k`: the hypothesis already exhibits a transversal of size
`m`.  The class is narrower than round 38's (`EdgelessOutside G m` implies that every branch vertex
of `G` lies in `H`, so round 38 gives `m + k`), so the content of Part 4 is the sharper constant
`m` on the degree-`0` class, and — in `JSP90.erdos73On_of_bounded_neighbourhood` — a constant that
is a function of Erdős's parameter alone.  No bound is assumed on the odd girth, on the packing
number, on the packing weight, or on the number of branch vertices. -/
theorem erdos73On_of_edgelessOutside (m k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      EdgelessOutside G m → CloseToBipartite m G :=
  fun _ _ G _ h => closeToBipartite_of_edgelessOutside h

/-- **IF ALL OF `G`'s EDGES TOUCH A SET OF AT MOST `k` VERTICES, `G` IS `k`-CLOSE TO BIPARTITE** —
the instance with `m = k` spelled out, so that the constant is a function of Erdős's parameter
alone. -/
theorem erdos73On_of_bounded_neighbourhood (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      EdgelessOutside G k → CloseToBipartite k G :=
  erdos73On_of_edgelessOutside k k

end Degree

end

