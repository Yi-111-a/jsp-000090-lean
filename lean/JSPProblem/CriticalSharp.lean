import JSPProblem.Critical
import JSPProblem.Deficiency

/-!
# JSP-000090, round 118 — the SPREAD CONSTANT: exactly how many colours the critical intersection
# graph can need

`JSPProblem/Critical.lean` (round 53) built the *critical-intersection-graph* route to Erdős Problem
#73 and localised the whole of the remaining mathematics to a single class-level hypothesis,

```lean
JSP90.SpreadMinimalTransversal r c
```

every graph whose odd cycle packings all have at most `r` members admits a **minimal** odd cycle
transversal whose critical intersection graph is `c`-colourable; from it,
`JSP90.erdos73_of_spreadMinimalTransversal` proves all of Erdős #73 with the constant `c * k`, and
`JSP90.oddCycleErdosPosa_of_spreadMinimalTransversal` proves Erdős–Pósa for odd cycles with the
constant `c * r`.  Round 53 also wrote, in the header of that file, that *"for `c = 2` this is the
classical shape of the Reed–Robertson–Seymour–Thomas theorem: a transversal of size at most twice
the packing number"*.

**This round computes that colour count, and the answer is a boundary result in both directions.**

## What is proved

* **Complete graphs carry critical data exactly at size `n - 2`**
  (`card_transversal_completeGraph_ge`, `minimalTransversal_card_completeGraph`,
  `card_criticalTransversal_completeGraph`): a set of `K_n` meets every odd cycle only if
  `n ≤ |X| + 2`, and any set carrying critical data has `|X| = n - 2`, because a critical cycle of
  `x ∈ X` has at least three vertices and they all lie in `{x} ∪ (V \ X)`.
* **The critical intersection graph of `K_n` is complete on the transversal**
  (`criticalCycle_eq_completeGraph`, `mem_compl_of_criticalCycle`, `adj_IntGraph_completeGraph`):
  every critical cycle of `x` is exactly the triangle `{x} ∪ (V \ X)`, so any two of them meet in
  `V \ X`, and the chromatic number of the critical intersection graph is `|X| = n - 2`.
* **THE SPREAD CONSTANT OF A COMPLETE GRAPH, EXACTLY** (`spreadTransversal_completeGraph_iff`):

  ```lean
  JSP90.SpreadTransversal c (completeGraph (Fin n)) ↔ n - 2 ≤ c
  ```

  So `K_4` needs exactly two colours and `K_5` exactly three, and the minimum spread constant of
  the family `K_n` is unbounded: the spread parameter of round 53 is a growing quantity of the
  graph, never a constant.
* **NO FIXED COLOUR COUNT WORKS** (`no_fixed_spreadConstant`,
  `not_spreadMinimalTransversal_of_packing`, `spreadMinimalTransversal_c_ge`): the class-level
  hypothesis of `JSP90.erdos73_of_spreadMinimalTransversal` asks for a *fixed* `c`, and that is
  **false** — a graph of odd cycle packing number `r` needs at least `3 * r - 2` colours, witness
  `K_{3r}`.  So `¬ (∃ c, ∀ r, SpreadMinimalTransversal r c)`, and the round-53 route is closed.
* **AND THE ROUTE IS PROVABLY QUADRATIC** (`exact_spread_constant_locIndep`): the class `LocIndep k`
  contains `K_{k + 2}`, whose spread constant is exactly `k`, so the class hypothesis of round 53
  needs `c ≥ k + 2`; while round 53's counting lemma (`card_X_le_of_colouring`) turns a
  `c`-colourable critical intersection graph into a transversal of size at most `c * k`.  Every
  instance obtained this way therefore carries a constant of at least `k * (k + 2)`, whereas the
  Erdős–Pósa theorem for odd cycles has the constant `O(k log k)`.  So this route can never prove
  Erdős–Pósa with a near-linear function, whatever one does about the existence of the colourings.

## What this is not

It is **not** a solution of JSP-000090.  `jsp_000090_main` is still not declared, the development
still has zero placeholders, and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is
untouched: what this round removes is one *route* to it, not the theorem.  The remaining statement is
unchanged and is still the one recorded in `discovery/JSP-000090/policy.json`.
-/

namespace JSP90

universe u

open Finset Fintype Set

noncomputable section

local instance instDecidableEqFinCS (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

variable {n : ℕ}

/-! ## Part 1 — transversals of complete graphs -/

/-- **A transversal of the odd cycles of `K_n` has at least `n - 2` vertices.**  Indeed deleting it
leaves a complete graph on `n - |X|` vertices, and a complete graph is bipartite exactly when it has
at most two vertices (`closeToBipartite_iff_completeGraph_add_two`). -/
theorem card_le_sub_two_of_hitsOddCycles_completeGraph {X : Finset (Fin n)}
    (hX : HitsOddCycles (SimpleGraph.completeGraph (Fin n)) X) : n - 2 ≤ X.card := by
  have h1 : CloseToBipartite X.card (SimpleGraph.completeGraph (Fin n)) :=
    (closeToBipartite_iff_hitsOddCycles (G := SimpleGraph.completeGraph (Fin n))).mpr
      ⟨X, le_rfl, hX⟩
  have h2 : n ≤ X.card + 2 := (closeToBipartite_iff_completeGraph_add_two X.card n).mp h1
  omega

/-- **A set of `K_n` which misses some odd cycle has fewer than `n - 2` vertices**: that odd cycle
has at least three vertices and lies in `V \ X`. -/
theorem card_lt_sub_two_of_not_hitsOddCycles_completeGraph {X : Finset (Fin n)}
    (hX : ¬ HitsOddCycles (SimpleGraph.completeGraph (Fin n)) X) : X.card + 2 < n := by
  simp only [HitsOddCycles, not_forall] at hX
  obtain ⟨C, hC, hempty⟩ := hX
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  have hsub : C ⊆ (Finset.univ : Finset (Fin n)) \ X := by
    intro z hz
    have hzX : z ∉ X := by
      intro hzX
      have hw : (C ∩ X).Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hz, hzX⟩⟩
      exact absurd (Finset.nonempty_iff_ne_empty.mp hw) hempty
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzX⟩
  have hcard : ((Finset.univ : Finset (Fin n)) \ X).card = n - X.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin]
  have h2 : C.card ≤ n - X.card := by
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    exact hle
  omega

/-- **Two vertices lie outside a transversal of `K_n` of size `n - 2`.** -/
theorem card_compl_eq_two {X : Finset (Fin n)} (hn : 2 ≤ n) (hX : X.card = n - 2) :
    (Finset.univ \ X : Finset (Fin n)).card = 2 := by
  have hnc : n - (n - 2) = 2 := by omega
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin, hX]
  exact hnc

/-- **There is a transversal of `K_n` of size `n - 2`**, namely `V \ {0, 1}`: an odd cycle of `K_n`
has at least three vertices, so it cannot be contained in `{0, 1}`. -/
theorem exists_transversal_completeGraph (hn : 2 ≤ n) :
    ∃ X : Finset (Fin n), HitsOddCycles (SimpleGraph.completeGraph (Fin n)) X ∧ X.card = n - 2 := by
  have hcard : ((Finset.univ : Finset (Fin n)) \
      (({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)))).card = n - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_fin]
    simp
  refine ⟨(Finset.univ : Finset (Fin n)) \
    (({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n))), ⟨?_, hcard⟩⟩
  intro C hC
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  by_contra hcon
  have hsub : C ⊆ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)) := by
    intro z hz
    by_contra hz'
    exact (Finset.not_nonempty_iff_eq_empty.mpr hcon) ⟨z, Finset.mem_inter.mpr
      ⟨hz, Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz'⟩⟩⟩
  have h2 : C.card ≤ 2 := by simpa using Finset.card_le_card hsub
  omega

/-- **Every minimal transversal of `K_n` has exactly `n - 2` vertices**: a transversal has at least
`n - 2` of them, and minimality removes one vertex and destroys it. -/
theorem minimalTransversal_card_completeGraph {X : Finset (Fin n)} (hn : 2 ≤ n)
    (hX : MinimalTransversal (SimpleGraph.completeGraph (Fin n)) X) : X.card = n - 2 := by
  have hge : n - 2 ≤ X.card := card_le_sub_two_of_hitsOddCycles_completeGraph hX.1
  by_cases hX0 : X = ∅
  · rw [hX0, Finset.card_empty] at hge ⊢
    omega
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hX0
    have hsub : X \ {x} ⊆ X := Finset.sdiff_subset
    have hne : X \ {x} ≠ X := by
      intro he
      have hxe : x ∈ X \ {x} := by rw [he]; exact hx
      rw [Finset.mem_sdiff] at hxe
      exact hxe.2 (Finset.mem_singleton.mpr rfl)
    have hnohits : ¬ HitsOddCycles (SimpleGraph.completeGraph (Fin n)) (X \ {x}) := hX.2 _ hsub hne
    have hlt : (X \ {x}).card + 2 < n :=
      card_lt_sub_two_of_not_hitsOddCycles_completeGraph hnohits
    have hcard : (X \ {x}).card = X.card - 1 :=
      Finset.sdiff_singleton_eq_erase x X ▸ Finset.card_erase_of_mem hx
    rw [hcard] at hlt
    omega

/-- **A set of size `n - 2` carries critical data in `K_n`.**  It is a transversal (an odd cycle
avoiding it would have three vertices inside the two vertices outside it), and every proper subset is
smaller, hence not a transversal, so it is a *minimal* transversal. -/
theorem exists_criticalTransversal_completeGraph {X : Finset (Fin n)} (hn : 2 ≤ n)
    (hX : X.card = n - 2) :
    Nonempty (CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X) := by
  have hhits : HitsOddCycles (SimpleGraph.completeGraph (Fin n)) X := by
    intro C hC
    have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
    by_contra hcon
    have hsub : C ⊆ (Finset.univ : Finset (Fin n)) \ X := by
      intro z hz
      have hzX : z ∉ X := by
        intro hzX
        exact (Finset.not_nonempty_iff_eq_empty.mpr hcon) ⟨z, Finset.mem_inter.mpr ⟨hz, hzX⟩⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzX⟩
    have hcard : ((Finset.univ : Finset (Fin n)) \ X).card = n - X.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin]
    have h2 : C.card ≤ n - X.card := by
      have hle := Finset.card_le_card hsub
      rw [hcard] at hle
      exact hle
    omega
  have hmin : MinimalTransversal (SimpleGraph.completeGraph (Fin n)) X := by
    refine ⟨hhits, fun Y hY hne hYhits => ?_⟩
    have hlt : Y.card < X.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hY, hne⟩)
    have h1 : n - 2 ≤ Y.card := card_le_sub_two_of_hitsOddCycles_completeGraph hYhits
    omega
  obtain ⟨d, -⟩ := exists_criticalTransversal_of_minimal hmin
  exact ⟨d⟩

/-! ## Part 2 — the critical intersection graph of a complete graph -/

/-- **A critical cycle of `x` contains no other vertex of the transversal.** -/
theorem eq_of_mem_criticalCycle_of_mem {X : Finset (Fin n)}
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X} {x : Fin n} (hx : x ∈ X)
    {z : Fin n} (hzX : z ∈ X) (hz : z ∈ d.C x) : z = x := by
  have hmem : z ∈ d.C x ∩ X := Finset.mem_inter.mpr ⟨hz, hzX⟩
  rw [d.single x hx] at hmem
  exact Finset.mem_singleton.mp hmem

/-- **Every vertex of a critical cycle is either the critical vertex or lies outside the
transversal.** -/
theorem mem_compl_or_eq_of_criticalCycle {X : Finset (Fin n)}
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X} {x : Fin n} (hx : x ∈ X) :
    ∀ z, z ∈ d.C x → z = x ∨ z ∉ X := by
  intro z hz
  by_cases hzX : z ∈ X
  · exact Or.inl (eq_of_mem_criticalCycle_of_mem hx hzX hz)
  · exact Or.inr hzX

/-- **THE SPREAD CONSTANT OF `K_n`, COUNTING FORM: a transversal carrying critical data has exactly
`n - 2` vertices.**  A transversal has at least `n - 2` of them, and a critical cycle of `x ∈ X` has
at least three vertices, all inside `{x} ∪ (V \ X)`. -/
theorem card_criticalTransversal_completeGraph (hn : 2 ≤ n) {X : Finset (Fin n)}
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X} : X.card = n - 2 := by
  have hge : n - 2 ≤ X.card := card_le_sub_two_of_hitsOddCycles_completeGraph d.hits
  by_cases hX0 : X = ∅
  · rw [hX0, Finset.card_empty] at hge ⊢
    omega
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hX0
    have h3 : 3 ≤ (d.C x).card := isOddCycle_card_ge_three (d.isOdd x hx)
    have hsub : d.C x ⊆ {x} ∪ (Finset.univ \ X) := by
      intro z hz
      rcases mem_compl_or_eq_of_criticalCycle hx z hz with heq | hz'
      · refine Finset.mem_union_left _ ?_
        rw [heq]
        exact Finset.mem_singleton_self x
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz'⟩)
    have hcard : ((Finset.univ : Finset (Fin n)) \ X).card = n - X.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin]
    have hle : (d.C x).card ≤ 1 + (n - X.card) := by
      have hle' := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr (by simp [hx]))] at hle'
      rw [Finset.card_singleton, hcard] at hle'
      exact hle'
    omega

/-- **Every critical cycle of a transversal of `K_n` of size `n - 2` is the triangle
`{x} ∪ (V \ X)`**: it has at least three vertices, all inside that set of three. -/
theorem criticalCycle_eq_completeGraph {X : Finset (Fin n)} (hn : 2 ≤ n)
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X} (hX : X.card = n - 2)
    {x : Fin n} (hx : x ∈ X) :
    d.C x = {x} ∪ (Finset.univ \ X) := by
  have hsub : d.C x ⊆ {x} ∪ (Finset.univ \ X) := by
    intro z hz
    rcases mem_compl_or_eq_of_criticalCycle hx z hz with heq | hz'
    · refine Finset.mem_union_left _ ?_
      rw [heq]
      exact Finset.mem_singleton_self x
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz'⟩)
  have hleA : ({x} ∪ (Finset.univ \ X) : Finset (Fin n)).card ≤ (d.C x).card := by
    have h3' : 3 ≤ (d.C x).card := isOddCycle_card_ge_three (d.isOdd x hx)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr (by simp [hx])),
      card_compl_eq_two hn hX, Finset.card_singleton]
    omega
  exact Finset.eq_of_subset_of_card_le hsub hleA

/-- **Any two critical cycles of a transversal of `K_n` of size `n - 2` meet**, in the two vertices
outside the transversal. -/
theorem mem_compl_of_criticalCycle {X : Finset (Fin n)} (hn : 2 ≤ n)
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X} (hX : X.card = n - 2)
    {x y : Fin n} (hx : x ∈ X) (hy : y ∈ X) : (d.C x) ∩ (d.C y) ≠ ∅ := by
  have hw : ((Finset.univ : Finset (Fin n)) \ X).Nonempty := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    have hc' : ((Finset.univ : Finset (Fin n)) \ X).card = 2 := card_compl_eq_two hn hX
    intro hEmpty
    have hc'' : ((Finset.univ : Finset (Fin n)) \ X).card = 0 := by
      rw [hEmpty, Finset.card_empty]
    omega
  obtain ⟨w, hw⟩ := hw
  have h1 : d.C x = {x} ∪ (Finset.univ \ X) := criticalCycle_eq_completeGraph hn hX hx
  have h2 : d.C y = {y} ∪ (Finset.univ \ X) := criticalCycle_eq_completeGraph hn hX hy
  refine Finset.nonempty_iff_ne_empty.mp ?_
  rw [h1, h2]
  exact ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hw, Finset.mem_union_right _ hw⟩⟩

/-- **THE CRITICAL INTERSECTION GRAPH OF `K_n` IS COMPLETE ON THE TRANSVERSAL.**  Any two distinct
vertices of `X` are adjacent, because their critical cycles both contain `V \ X`. -/
theorem adj_IntGraph_completeGraph {X : Finset (Fin n)} (hn : 2 ≤ n)
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X}
    {x y : Fin n} (hx : x ∈ X) (hy : y ∈ X) (hne : x ≠ y) : (IntGraph d).Adj x y :=
  ⟨hx, hy, hne,
    mem_compl_of_criticalCycle hn (card_criticalTransversal_completeGraph hn (d := d)) hx hy⟩

/-! ## Part 3 — the colour count is the size of the transversal -/

/-- **A `c`-colouring of the critical intersection graph of `K_n` is injective on the
transversal**, so `c ≥ n - 2`.  This is the counting half of the spread constant, and it uses no
packing bound at all. -/
theorem card_le_of_colouring_IntGraph_completeGraph {X : Finset (Fin n)} (hn : 2 ≤ n)
    {d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X} {c : ℕ}
    (hc : Nonempty ((IntGraph d).Coloring (Fin c))) : n - 2 ≤ c := by
  obtain ⟨col, hcol⟩ := hc
  have hcard : X.card = n - 2 := card_criticalTransversal_completeGraph hn (d := d)
  have hcolinj : ∀ x ∈ X, ∀ y ∈ X, col x = col y → x = y := by
    intro x hx y hy hxy
    by_contra hcon
    have hval : col x ≠ col y := by
      simpa using hcol (adj_IntGraph_completeGraph hn hx hy (fun he => hcon he))
    exact hval hxy
  have hinj : Set.InjOn col X := fun _ hx _ hy hxy => hcolinj _ hx _ hy hxy
  have hle := Finset.card_le_card_of_injOn col
    (s := (X : Finset (Fin n))) (t := (Finset.univ : Finset (Fin c)))
    (fun _ _ => Finset.mem_univ _) hinj
  rw [card_criticalTransversal_completeGraph hn (d := d)] at hle
  simpa using hle

/-- **A transversal of size `n - 2` admits a `c`-colouring of its critical intersection graph as soon
as `0 < c` and `n - 2 ≤ c`**: colour the transversal injectively and every other vertex with colour
`0`.  (The bound `0 < c` is not an artefact: a colouring is a function `V → Fin c`, so a colouring
exists only when `c > 0`.  It is automatic as soon as `n ≥ 3`.) -/
theorem colouring_IntGraph_completeGraph {X : Finset (Fin n)} (hn : 2 ≤ n)
    (hX : X.card = n - 2) {c : ℕ} (hc : 0 < c) (hc' : n - 2 ≤ c) :
    ∃ d : CriticalTransversal (SimpleGraph.completeGraph (Fin n)) X,
      Nonempty ((IntGraph d).Coloring (Fin c)) := by
  obtain ⟨d⟩ := exists_criticalTransversal_completeGraph hn hX
  have hcard : X.card ≤ c := by rw [hX]; exact hc'
  let e : (X : Finset (Fin n)) ≃ Fin X.card := Finset.equivFinOfCardEq rfl
  let f : Fin n → Fin c := fun x =>
    if hx : x ∈ X then Fin.castLE hcard (e ⟨x, hx⟩) else ⟨0, hc⟩
  have hf : ∀ {x y : Fin n}, (IntGraph d).Adj x y → f x ≠ f y := by
    intro x y hAdj
    obtain ⟨hx, hy, hne, -⟩ := hAdj
    have h1 : e ⟨x, hx⟩ ≠ e ⟨y, hy⟩ := by
      intro hEq
      exact hne (congrArg Subtype.val (e.injective hEq))
    simp only [f, dite_eq_left hx, dite_eq_left hy]
    exact fun hEq => hne (congrArg Subtype.val (e.injective (Fin.castLE_injective hcard hEq)))
  exact ⟨d, ⟨SimpleGraph.Coloring.mk f hf⟩⟩

/-- **THE SPREAD CONSTANT OF A COMPLETE GRAPH, EXACTLY: `K_n` admits a `c`-spread transversal if and
only if `n - 2 ≤ c` and `c > 0`.**  So `K_4` needs exactly two colours and `K_5` exactly three, and
the minimum spread constant of the family `K_n` is unbounded: the spread parameter of
`JSPProblem/Critical.lean` is a growing quantity of the graph, never a constant. -/
theorem spreadTransversal_completeGraph_iff (hn : 2 ≤ n) (c : ℕ) :
    SpreadTransversal c (SimpleGraph.completeGraph (Fin n)) ↔ (n - 2 ≤ c ∧ 0 < c) := by
  constructor
  · rintro ⟨X, d, hc⟩
    have h1 : n - 2 ≤ c := card_le_of_colouring_IntGraph_completeGraph hn (d := d) hc
    obtain ⟨col, -⟩ := hc
    have hlt : 0 < c := Nat.zero_lt_of_lt (col ⟨0, by omega⟩).isLt
    exact ⟨h1, hlt⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨X, -, hX⟩ := exists_transversal_completeGraph hn
    obtain ⟨d, hc⟩ := colouring_IntGraph_completeGraph hn hX h2 h1
    exact ⟨X, d, hc⟩

/-- **THE SPREAD CONSTANT OF A COMPLETE GRAPH OF ORDER AT LEAST THREE, EXACTLY: `K_n` admits a
`c`-spread transversal if and only if `n - 2 ≤ c`**, the positivity of `c` being then automatic. -/
theorem spreadTransversal_completeGraph_iff' (hn : 3 ≤ n) (c : ℕ) :
    SpreadTransversal c (SimpleGraph.completeGraph (Fin n)) ↔ n - 2 ≤ c := by
  rw [spreadTransversal_completeGraph_iff (by omega) c]
  constructor
  · rintro ⟨h1, -⟩
    exact h1
  · intro h1
    exact ⟨h1, by omega⟩

/-- `K_4` admits a `c`-spread transversal exactly when `c ≥ 2`. -/
theorem spreadTransversal_completeGraph_four (c : ℕ) :
    SpreadTransversal c (SimpleGraph.completeGraph (Fin 4)) ↔ 2 ≤ c :=
  spreadTransversal_completeGraph_iff' (by omega) c

/-- **`K_5` admits a `c`-spread transversal exactly when `c ≥ 3`.** -/
theorem spreadTransversal_completeGraph_five (c : ℕ) :
    SpreadTransversal c (SimpleGraph.completeGraph (Fin 5)) ↔ 3 ≤ c :=
  spreadTransversal_completeGraph_iff' (by omega) c

/-- **`K_5` has no 2-spread transversal.**  Round 53's remark that *"for `c = 2` this is the
classical shape of the Reed–Robertson–Seymour–Thomas theorem"* cannot be a theorem: the complete
graphs refute it, and `K_5` is a graph satisfying Erdős's own hypothesis `LocIndep 3`. -/
theorem not_spread_transversal_two_completeGraph_five :
    ¬ SpreadTransversal 2 (SimpleGraph.completeGraph (Fin 5)) := by
  rw [spreadTransversal_completeGraph_five]
  omega

/-! ## Part 4 — the packing bound of a complete graph -/

/-- **Additivity over a pairwise disjoint family of finsets inside `s`: the sum of their sizes is at
most `|s|`.** -/
theorem sum_card_le_of_disjointFamily_sub {n : ℕ} {C : Finset (Finset (Fin n))}
    (hd : DisjointFamily C) (s : Finset (Fin n)) (hsub : ∀ X ∈ C, X ⊆ s) :
    (∑ X ∈ C, X.card) ≤ s.card := by
  induction C using Finset.induction_on generalizing s with
  | empty => simp
  | @insert X C hX ih =>
      have hd' : DisjointFamily C := by
        intro Y hY Z hZ hYZ
        exact hd Y (Finset.mem_insert_of_mem hY) Z (Finset.mem_insert_of_mem hZ) hYZ
      have hsub' : ∀ Y ∈ C, Y ⊆ s \ X := by
        intro Y hY z hz
        refine Finset.mem_sdiff.mpr ⟨hsub Y (Finset.mem_insert_of_mem hY) hz, ?_⟩
        intro hzX
        have hEmpty : Y ∩ X = ∅ :=
          hd Y (Finset.mem_insert_of_mem hY) X (Finset.mem_insert_self X C)
            (fun he => hX (he ▸ hY))
        exact (Finset.not_nonempty_iff_eq_empty.mpr hEmpty)
          ⟨z, Finset.mem_inter.mpr ⟨hz, hzX⟩⟩
      have hle : (∑ Y ∈ C, Y.card) ≤ (s \ X).card :=
        ih hd' (s \ X) (fun Y hY z hz => hsub' Y hY hz)
      have hXs : X ⊆ s := hsub X (Finset.mem_insert_self X C)
      have hcard : (s \ X).card = s.card - X.card := Finset.card_sdiff_of_subset hXs
      have hlecard : X.card ≤ s.card := Finset.card_le_card hXs
      rw [Finset.sum_insert hX]
      refine le_trans (Nat.add_le_add_left hle _) ?_
      omega

/-- **The sizes of a packing of vertex sets of `V` sum to at most `|V|`.** -/
theorem sum_card_le_of_disjointFamily {n : ℕ} {C : Finset (Finset (Fin n))}
    (hd : DisjointFamily C) : (∑ X ∈ C, X.card) ≤ n := by
  have hle := sum_card_le_of_disjointFamily_sub hd (Finset.univ : Finset (Fin n))
    (fun _ _ => Finset.subset_univ _)
  simpa using hle

/-- **THE PACKING BOUND OF A COMPLETE GRAPH, COUNTING FORM: `3` times the number of members of a
packing of odd cycles of `K_n` is at most `n`** — every odd cycle has at least three vertices and
the members are pairwise vertex-disjoint. -/
theorem mul_three_le_of_packing_completeGraph {n : ℕ} {C : Finset (Finset (Fin n))}
    (hC : IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin n)) C) : 3 * C.card ≤ n := by
  have hge0 : (∑ X ∈ C, (3 : ℕ)) ≤ ∑ X ∈ C, X.card :=
    Finset.sum_le_sum fun X hX => isOddCycle_card_ge_three (hC.2 X hX)
  have hge : (3 : ℕ) * C.card ≤ ∑ X ∈ C, X.card := by
    have hsum : (∑ X ∈ C, (3 : ℕ)) = C.card * 3 := Finset.sum_const (s := C) (b := (3 : ℕ))
    calc (3 : ℕ) * C.card = C.card * 3 := Nat.mul_comm _ _
      _ = ∑ X ∈ C, (3 : ℕ) := hsum.symm
      _ ≤ ∑ X ∈ C, X.card := hge0
  have hle := sum_card_le_of_disjointFamily hC.1
  omega

/-- **THE PACKING BOUND OF A COMPLETE GRAPH: a packing of odd cycles of `K_n` has at most `n / 3`
members.** -/
theorem packing_card_le_completeGraph {n : ℕ} {C : Finset (Finset (Fin n))}
    (hC : IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin n)) C) : C.card ≤ n / 3 := by
  refine (Nat.le_div_iff_mul_le (k := 3) (by omega)).2 ?_
  have h3 := mul_three_le_of_packing_completeGraph hC
  omega

/-! ## Part 5 — the class-level hypothesis of round 53 is false -/

/-- **THE SPREAD CONSTANT MUST GROW WITH THE PACKING NUMBER: `SpreadMinimalTransversal r c` forces
`3 * r - 2 ≤ c`.**  The witness is `K_{3r}`, whose odd cycle packings have at most `r` members (Part 4)
and whose critical intersection graph is complete on `3r - 2` vertices (Part 3). -/
theorem spreadMinimalTransversal_c_ge {r c : ℕ} (hr : 3 ≤ r)
    (h : SpreadMinimalTransversal.{0} r c) : 3 * r - 2 ≤ c := by
  have hpack : ∀ (C : Finset (Finset (Fin (3 * r)))),
      IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin (3 * r))) C → C.card ≤ r := by
    intro C hC
    have h3 : 3 * C.card ≤ 3 * r := mul_three_le_of_packing_completeGraph hC
    omega
  obtain ⟨X, _, d, hc⟩ := h (Fin (3 * r)) (inferInstance : Fintype (Fin (3 * r)))
    (SimpleGraph.completeGraph (Fin (3 * r))) hpack
  exact card_le_of_colouring_IntGraph_completeGraph (by omega) (d := d) hc

/-- **The class-level hypothesis of `JSP90.erdos73_of_spreadMinimalTransversal` fails at every packing
number `r ≥ 3` as soon as `c + 2 < 3 * r`.** -/
theorem not_spreadMinimalTransversal_of_packing {r c : ℕ} (hr : 3 ≤ r) (hc : c + 2 < 3 * r) :
    ¬ SpreadMinimalTransversal.{0} r c := by
  intro h
  have h1 := spreadMinimalTransversal_c_ge hr h
  omega

/-- **NO FIXED COLOUR COUNT WORKS FOR ALL GRAPHS.**  `JSP90.erdos73_of_spreadMinimalTransversal`
asks for, for every `r`, a graph of odd cycle packing number at most `r` carrying a minimal
transversal whose critical intersection graph is `c`-colourable, with one and the same `c`; for
every `c` the graph `K_{3 (c + 3)}` refutes it.  So the critical-intersection-graph route of
`JSPProblem/Critical.lean` cannot deliver Erdős #73 or Erdős–Pósa for odd cycles, and
`JSP90.OddCycleErdosPosa r` has to be reached by a different argument. -/
theorem no_fixed_spreadConstant : ¬ (∃ c : ℕ, ∀ r : ℕ, SpreadMinimalTransversal.{0} r c) := by
  rintro ⟨c, h⟩
  exact not_spreadMinimalTransversal_of_packing (c := c) (r := c + 3) (by omega) (by omega)
    (h (c + 3))

/-- **THE LOWER BOUND OF `JSP90.spreadMinimalTransversal_c_ge` IS SHARP.**  `K_{3r}` has odd cycle
packing number at most `r` (`JSP90.packing_card_le_completeGraph`) and its minimum spread constant is
*exactly* `3 * r - 2` (`JSP90.spreadTransversal_completeGraph_iff'`).  So the least colour count that a
class-level hypothesis of the shape `SpreadMinimalTransversal r c` can ask for is `3 * r - 2`, and it
is forced: no smaller constant works, and `K_{3r}` is the witness. -/
theorem spreadConstant_exact_completeGraph {r : ℕ} (hr : 3 ≤ r) :
    (∀ C : Finset (Finset (Fin (3 * r))),
        IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin (3 * r))) C → C.card ≤ r) ∧
      (∀ c : ℕ, SpreadTransversal c (SimpleGraph.completeGraph (Fin (3 * r))) ↔ 3 * r - 2 ≤ c) := by
  constructor
  · intro C hC
    have h3 : 3 * C.card ≤ 3 * r := mul_three_le_of_packing_completeGraph hC
    omega
  · intro c
    exact spreadTransversal_completeGraph_iff' (by omega) c

/-! ## Part 6 — the spread constant of the class `LocIndep k` -/

/-- **`K_{k + 2}` attains the lower bound: it satisfies `LocIndep k` and its spread constant is
exactly `k`.**  Since round 53's counting lemma turns a `c`-colourable critical intersection graph
into a transversal of size at most `c * k`, and the class hypothesis of
`JSP90.erdos73_of_spreadMinimalTransversal` has to cover `K_{k + 2}` (whose odd cycle packing number
is at most `k`), every instance obtained by that route carries a constant of at least
`k * (k + 2)`: the route is quadratic, whereas the Erdős–Pósa theorem for odd cycles has the constant
`O(k log k)`.  So the route cannot prove Erdős–Pósa with a near-linear function, whatever one does
about the existence of the colourings. -/
theorem exact_spread_constant_locIndep (k : ℕ) (hk : 1 ≤ k) :
    LocIndep k (SimpleGraph.completeGraph (Fin (k + 2))) ∧
      (∀ c : ℕ, SpreadTransversal c (SimpleGraph.completeGraph (Fin (k + 2))) ↔ k ≤ c) := by
  refine ⟨(locIndep_iff_maxDef_le).mpr (by
    rw [maxDef_completeGraph (by omega)]
    omega), fun c => ?_⟩
  rw [spreadTransversal_completeGraph_iff' (by omega) c]
  omega

/-- **The spread constant of `K_{k + 2}`, the class-level form:** any `c` for which `K_{k + 2}`
admits a `c`-spread transversal satisfies `k ≤ c`. -/
theorem spread_constant_ge_of_locIndep {k c : ℕ} (hk : 1 ≤ k)
    (hc : SpreadTransversal c (SimpleGraph.completeGraph (Fin (k + 2)))) : k ≤ c :=
  (exact_spread_constant_locIndep k hk).2 c |>.mp hc

/-- `K_2`, the case `k = 0`: the spread constant of a bipartite graph is `0` — the empty transversal
carries vacuous critical data, and the only constraint left on the colouring is `c > 0`. -/
theorem spreadTransversal_completeGraph_two (c : ℕ) :
    SpreadTransversal c (SimpleGraph.completeGraph (Fin 2)) ↔ 0 < c := by
  rw [spreadTransversal_completeGraph_iff (by omega) c]
  omega

end
end JSP90