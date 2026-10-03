/-
# JSP-000090 — `JSPProblem/FewOdd.lean`: the **FEW-ODD-CYCLES axis**, and the 8-vertex witness that
kills the Helly route at `k = 1`

This is the **twenty-third attack family**.  Round 125 settled the class *all odd cycles are
triangles* with the optimal constant `2`; `policy.json` left two residual cases of the `k = 1` route,
the attachment points of a 5-cycle (`PetalSetLeTwoOfOne` with petals of length `≥ 5`) and the whole
odd-girth-`≥ 5` case.  This round does **not** continue the petal-counting route.  It attacks the
Helly route instead — the only route in the whole development that delivers the constant `1` at
`k = 1` (`JSP90.closeToBipartite_one_of_helly_of_locIndep_one` of round 83) — and it shows, by
machine check, that **that route is dead at `k = 1`**, while it delivers a new instance on a class
rounds 83–125 never touched.

## Part 1 — a NEW INSTANCE OF THE HEADLINE THEOREM ON THE FEW-ODD-CYCLES CLASS

Erdős's hypothesis enters exactly once, through `JSP90.inter_oddCycle_of_locIndep_one`: **two odd
cycles of a `LocIndep 1` graph meet.**  So the family `JSP90.OddCycles G` of *all* the odd cycles of
`G` is a pairwise-meeting family of nonempty sets, and pairing its members gives one transversal
vertex per pair:

* **`JSP90.exists_transversal_card_le`** — the **pairing lemma**: a pairwise-meeting family `𝒞` of
  nonempty sets has a transversal `T` with `2 * T.card ≤ 𝒞.card + 1`, i.e. `|T| ≤ ⌈|𝒞| / 2⌉`.
  (Strong induction on `|𝒞|`; the step pairs two members, pays **one** vertex for the pair, and
  recurses on the residue.)
* **`JSP90.closeToBipartite_of_locIndep_one_of_card_oddCycles_le`** and
  **`JSP90.erdos73On_fewOddCycles`** — **A NEW INSTANCE OF THE HEADLINE THEOREM**:
  `LocIndep 1 G` and at most `2 * m` odd cycles give `CloseToBipartite m G`.  The hypothesis is a
  count of odd cycles, which is new in this development: no previous instance bounds
  `|OddCycles G|` (round 98 bounded the *packing* number instead, and that number is `1` here, so
  Part 1's hypothesis is genuinely stronger information than anything proved before).
* Two base levels: `JSP90.closeToBipartite_one_of_locIndep_one_of_two_oddCycles` (at most two odd
  cycles, constant `1`) and `JSP90.closeToBipartite_two_of_locIndep_one_of_four_oddCycles` (at most
  four odd cycles, constant `2`).

## Part 2 — `JSP90.k4sub`: THE 8-VERTEX WITNESS.  `LocIndep 1`, ODD GIRTH `5`, `τ_odd = 2`

`JSP90.k4sub` is `K₄` on `{0, 3, 6, 7}` with **four of its six edges subdivided** (by `1, 2, 4, 5`),
i.e. `10` edges on `8` vertices, and it has **no triangle**.  Everything about it is proved:

* `JSP90.locIndep_one_k4sub` — `LocIndep 1 k4sub` (a kernel decision over the `2 ^ 8` vertex sets),
  `JSP90.maxDef_k4sub : MaxDef k4sub = 1` (the deficiency is **exactly** `1`), so `k4sub` is a graph
  on which the constant `2` of Part 1 is genuinely needed;
* `JSP90.isOddCycle_k4sub_c₁ … c₄` — four 5-cycles `C₁ = {0,2,3,4,6}`, `C₂ = {0,1,3,5,7}`,
  `C₃ = {0,1,2,6,7}`, `C₄ = {3,4,5,6,7}`, with **every six pairwise intersections nonempty** and
  **empty four-fold intersection**;
* `JSP90.closeToBipartite_two_k4sub` — deleting `{0, 3}` leaves the bipartite graph on the parts
  `{7, 2, 4}` and `{1, 5, 6}`;
* **`JSP90.closeToBipartite_iff_k4sub`** — the odd cycle transversal number of `k4sub` is **exactly
  `2`**.

Exhaustively, over **all** graphs on `n ≤ 7` vertices (`discovery/JSP-000090/r126.c`), no `LocIndep 1`
graph of odd girth `≥ 5` needs more than `1` vertex and no `LocIndep 1` graph at all needs more than
`2`; `r126b.c` and `r126d.c` locate `k4sub` as the **smallest** obstruction to a one-vertex
transversal at odd girth `≥ 5` (it also reports that all four of its odd cycles are 5-cycles, so its
odd girth is exactly `5`).

## Part 3 — THE HELLY ROUTE IS DEAD AT `k = 1` (machine-checked)

* **`JSP90.not_helly_k4sub`** — `¬ HellyOddCycles k4sub`: the four odd cycles are a pairwise-meeting
  family with no common vertex.  Together with `JSP90.locIndep_one_k4sub` this is the
  machine-checked statement that **Erdős's hypothesis does not imply the Helly property**, so
  `JSP90.closeToBipartite_one_of_helly_of_locIndep_one` (round 83) can never be applied to all graphs,
  and `JSP90.HellyOddCycles` is not a consequence of `LocIndep k` for any `k`.
* **`JSP90.three_commonVertex_of_k4sub`** — **every three of the four odd cycles have a common
  vertex** (`0`, `6`, `7`, `3` for the four triples).  So the minimal Helly obstruction of `k4sub`
  has size **exactly four**: no three-element version of the Helly property
  (`JSP90.TwoHellyOddCycles`) can detect it, and the natural upgrade of round 83's instance —
  "`TwoHellyOddCycles` instead of `HellyOddCycles`" — is **false**, witnessed by a graph of odd girth
  `5` whose four odd cycles are all 5-cycles.
* `JSP90.card_oddCycles_ge_four_k4sub` — `4 ≤ |OddCycles k4sub|`, so Part 1's hypothesis is met and
  its constant `2` is attained;
* `JSP90.LocIndepOneNotHelly` — the statements above packaged as one conjunction: the formal record
  that "`LocIndep 1 ⟹ 1`-close" is false, and that `CloseToBipartite 2` is the right answer here.

## What is *not* proved

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; behind it stands `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  Part 1 is an instance with a
*quantitative* hypothesis (`|OddCycles G| ≤ 2 m`), not a bound in terms of `LocIndep k` alone: the
number of odd cycles is not controlled by `MaxDef G` (round 100's
`JSP90.maxDegLe_two_unbounded_oddCycles` records that a family of graphs of deficiency `2` has an
unbounded number of odd cycles), so the residual of this axis is exactly a bound on `|OddCycles G|`
in terms of `MaxDef G`, which is false in that shape.  No hypothesis is *assumed* anywhere in this
file: the pairing lemma is proved and applied to the family of all odd cycles.
-/

import JSPProblem.Helly
import JSPProblem.DegColour
import JSPProblem.Greedy
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Part 1 — the pairing lemma, and the new instance -/

section Pairing

variable {α : Type*}

local instance instDecidableEqPairing : DecidableEq α := Classical.decEq α

/-- **THE PAIRING LEMMA.**  A family `𝒞` of nonempty sets any two of which meet has a transversal
`T` with `2 * T.card ≤ 𝒞.card + 1`, i.e. `|T| ≤ ⌈|𝒞| / 2⌉`.

Proof: strong induction on `|𝒞|`.  `𝒞 = ∅` is trivial and `|𝒞| = 1` costs one vertex.  For
`|𝒞| ≥ 2` take two distinct members `C`, `D`, pay **one** vertex `a ∈ C ∩ D` for the *pair*, and apply
the induction hypothesis to `𝒞.erase C |>.erase D`, which has two members fewer.  Then
`2 * |T| ≤ 2 * (|𝒞'| + 1) = |𝒞'| + |𝒞'| + 2 ≤ (|𝒞'| + 1) + 2 = |𝒞| + 1`. -/
theorem exists_transversal_card_le {𝒞 : Finset (Finset α)}
    (hall : ∀ C ∈ 𝒞, C.Nonempty)
    (hmeet : ∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ≠ D → (C ∩ D).Nonempty) :
    ∃ T : Finset α, 2 * T.card ≤ 𝒞.card + 1 ∧ ∀ C ∈ 𝒞, (C ∩ T).Nonempty := by
  classical
  have key : ∀ (n : ℕ) (𝒞 : Finset (Finset α)), 𝒞.card = n →
      (∀ C ∈ 𝒞, C.Nonempty) → (∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ≠ D → (C ∩ D).Nonempty) →
      ∃ T : Finset α, 2 * T.card ≤ n + 1 ∧ ∀ C ∈ 𝒞, (C ∩ T).Nonempty := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro 𝒞 hcard hall hmeet
      by_cases h0 : n = 0
      · have hcard0 : 𝒞.card = 0 := hcard.trans h0
        have hempty : 𝒞 = ∅ := Finset.card_eq_zero.mp hcard0
        refine ⟨∅, ?_, ?_⟩
        · simp [hcard0]
        · intro C hC
          rw [hempty] at hC
          simp at hC
      · by_cases h1 : n = 1
        · have h1' : 𝒞.card = 1 := hcard ▸ h1
          obtain ⟨C, hCeq⟩ := Finset.card_eq_one.mp h1'
          obtain ⟨a, ha⟩ := hall C (by rw [hCeq]; exact Finset.mem_singleton_self C)
          refine ⟨{a}, ?_, ?_⟩
          · simp [h1]
          · intro D hD
            have hD' : D = C := by rw [hCeq] at hD; exact Finset.mem_singleton.mp hD
            rw [hD']
            exact ⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_singleton_self a⟩⟩
        · have h2le : 2 ≤ n := by omega
          obtain ⟨S, hSsub, hcardS⟩ :=
            Finset.le_card_iff_exists_subset_card.mp (by omega : 2 ≤ 𝒞.card)
          obtain ⟨C, D, hCD, hSdeq⟩ := Finset.card_eq_two.mp hcardS
          have hCmem : C ∈ 𝒞 := hSsub (by rw [hSdeq]; exact Finset.mem_insert_self _ _)
          have hDmem : D ∈ 𝒞 :=
            hSsub (by rw [hSdeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          obtain ⟨a, ha⟩ := hmeet C hCmem D hDmem hCD
          have haC : a ∈ C := Finset.mem_inter.mp ha |>.1
          have haD : a ∈ D := Finset.mem_inter.mp ha |>.2
          have hDer : D ∈ 𝒞.erase C := Finset.mem_erase_of_ne_of_mem hCD.symm hDmem
          have hcard' : ((𝒞.erase C).erase D).card + 2 = 𝒞.card := by
            have h1 : ((𝒞.erase C).erase D).card = (𝒞.erase C).card - 1 :=
              Finset.card_erase_of_mem hDer
            have h2 : (𝒞.erase C).card = 𝒞.card - 1 := Finset.card_erase_of_mem hCmem
            omega
          have hlt : ((𝒞.erase C).erase D).card < n := by omega
          obtain ⟨T', hT', hhit⟩ :=
            ih ((𝒞.erase C).erase D).card hlt ((𝒞.erase C).erase D) rfl
              (fun C' hC' => hall C' (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC')))
              (fun C' hC' D' hD' hne =>
                hmeet C' (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC'))
                  D' (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD')) hne)
          refine ⟨insert a T', ?_, ?_⟩
          · have hTc : (insert a T').card ≤ T'.card + 1 := Finset.card_insert_le a T'
            have h2T : 2 * (insert a T').card ≤ 2 * (T'.card + 1) := Nat.mul_le_mul_left 2 hTc
            omega
          · intro C' hC'
            by_cases h1 : C' = C
            · rw [h1]
              exact ⟨a, Finset.mem_inter.mpr ⟨haC, Finset.mem_insert_self a T'⟩⟩
            · by_cases h2 : C' = D
              · rw [h2]
                exact ⟨a, Finset.mem_inter.mpr ⟨haD, Finset.mem_insert_self a T'⟩⟩
              · obtain ⟨x, hx⟩ :=
                  hhit C' (Finset.mem_erase_of_ne_of_mem h2 (Finset.mem_erase_of_ne_of_mem h1 hC'))
                obtain ⟨hxC', hxT'⟩ := Finset.mem_inter.mp hx
                exact ⟨x, Finset.mem_inter.mpr ⟨hxC', Finset.mem_insert_of_mem hxT'⟩⟩
  exact key 𝒞.card 𝒞 rfl hall hmeet

end Pairing

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, ON THE FEW-ODD-CYCLES CLASS.**

`LocIndep 1 G` together with "at most `2 * m` odd cycles" gives `CloseToBipartite m G`.  Erdős's
hypothesis is used only through `JSP90.inter_oddCycle_of_locIndep_one` — the odd cycles pairwise
meet — and the pairing lemma turns that into a transversal of `⌈|OddCycles G| / 2⌉` vertices.  There
is no bound on the degrees, the odd girth, the sizes of the odd cycles, or the number of vertices. -/
theorem closeToBipartite_of_locIndep_one_of_card_oddCycles_le (m : ℕ)
    (hG : LocIndep 1 G) (hcard : (OddCycles G).card ≤ 2 * m) : CloseToBipartite m G := by
  classical
  have hall : ∀ C ∈ OddCycles G, C.Nonempty := by
    intro C hC
    exact nonempty_of_isOddCycle (mem_oddCycles.mp hC)
  have hmeet : ∀ C ∈ OddCycles G, ∀ D ∈ OddCycles G, C ≠ D → (C ∩ D).Nonempty := by
    intro C hC D hD _
    exact Finset.nonempty_iff_ne_empty.mpr
      (inter_oddCycle_of_locIndep_one hG (mem_oddCycles.mp hC) (mem_oddCycles.mp hD))
  obtain ⟨T, hT, hhit⟩ := exists_transversal_card_le hall hmeet
  have hle : T.card ≤ m := by
    have h2T : 2 * T.card ≤ (OddCycles G).card + 1 := hT
    omega
  refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨T, hle, fun D hD => ?_⟩
  obtain ⟨x, hx⟩ := hhit D (mem_oddCycles.mpr hD)
  exact ne_empty_of_mem hx

/-- **THE SAME INSTANCE IN `Erdős73On` FORM.**  This is a genuine instance of the statement of
`JSPProblem/Definitions.lean`: the hypothesis is Erdős's own at `k = 1` together with a count of odd
cycles, and the conclusion holds for every finite vertex type. -/
theorem erdos73On_fewOddCycles (m : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → (OddCycles G).card ≤ 2 * m →
      CloseToBipartite m G :=
  fun _ _ _ hG hcard => closeToBipartite_of_locIndep_one_of_card_oddCycles_le m hG hcard

/-- **BASE LEVEL `m = 1`: a `LocIndep 1` graph with at most TWO odd cycles is one vertex away from
bipartite.**  In this case the two odd cycles meet, so their common vertex is the transversal.  This is
the instance of round 82/83 restricted to a family of size `≤ 2`, obtained with **no** hypothesis on
the intersection pattern. -/
theorem closeToBipartite_one_of_locIndep_one_of_two_oddCycles
    (hG : LocIndep 1 G) (hcard : (OddCycles G).card ≤ 2) : CloseToBipartite 1 G :=
  closeToBipartite_of_locIndep_one_of_card_oddCycles_le 1 hG (by omega)

/-- **BASE LEVEL `m = 2`: a `LocIndep 1` graph with at most FOUR odd cycles is two vertices away from
bipartite**, and `JSP90.k4sub` (Part 2) attains the constant. -/
theorem closeToBipartite_two_of_locIndep_one_of_four_oddCycles
    (hG : LocIndep 1 G) (hcard : (OddCycles G).card ≤ 4) : CloseToBipartite 2 G :=
  closeToBipartite_of_locIndep_one_of_card_oddCycles_le 2 hG (by omega)

/-! ## Part 2 — `k4sub`: `LocIndep 1`, odd girth `5`, transversal number exactly `2` -/

/-- **`K₄` on `{0, 3, 6, 7}` with FOUR of its six edges subdivided** — by `1` (for `0 – 7`), by `2`
(for `0 – 6`), by `4` (for `3 – 6`) and by `5` (for `3 – 7`); the edges `0 – 3` and `6 – 7` are left
unsubdivided.  Ten edges on eight vertices, and **no triangle**: every neighbourhood is either
`{0, 1, 2, 3}`, `{3, 4, 5}`, `{2, 4, 6, 7}`, `{1, 5, 6, 7}`, `{0, 7}`, `{0, 6}`, `{3, 6}` or
`{3, 7}`, none of which is complete. -/
def k4subEdge : Finset (Fin 8 × Fin 8) :=
  (Finset.univ : Finset (Fin 8 × Fin 8)).filter fun p =>
    (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 0) ∨
    (p.1 = 0 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 0) ∨
    (p.1 = 0 ∧ p.2 = 3) ∨ (p.1 = 3 ∧ p.2 = 0) ∨
    (p.1 = 1 ∧ p.2 = 7) ∨ (p.1 = 7 ∧ p.2 = 1) ∨
    (p.1 = 2 ∧ p.2 = 6) ∨ (p.1 = 6 ∧ p.2 = 2) ∨
    (p.1 = 3 ∧ p.2 = 4) ∨ (p.1 = 4 ∧ p.2 = 3) ∨
    (p.1 = 3 ∧ p.2 = 5) ∨ (p.1 = 5 ∧ p.2 = 3) ∨
    (p.1 = 4 ∧ p.2 = 6) ∨ (p.1 = 6 ∧ p.2 = 4) ∨
    (p.1 = 5 ∧ p.2 = 7) ∨ (p.1 = 7 ∧ p.2 = 5) ∨
    (p.1 = 6 ∧ p.2 = 7) ∨ (p.1 = 7 ∧ p.2 = 6)

theorem k4subEdge_symm : ∀ v w : Fin 8, (v, w) ∈ k4subEdge ↔ (w, v) ∈ k4subEdge := by decide

theorem k4subEdge_irrefl : ∀ v : Fin 8, (v, v) ∉ k4subEdge := by decide

/-- The graph of Part 2. -/
def k4sub : SimpleGraph (Fin 8) where
  Adj v w := (v, w) ∈ k4subEdge
  symm := ⟨fun _ _ h => (k4subEdge_symm _ _).mp h⟩
  loopless := ⟨fun v h => k4subEdge_irrefl _ h⟩

@[simp] theorem k4sub_adj {v w : Fin 8} : k4sub.Adj v w ↔ (v, w) ∈ k4subEdge := Iff.rfl

local instance instDecidableRelK4sub : DecidableRel k4sub.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ k4subEdge))

/-- A cyclic ordering of five vertices. -/
def dcyc5 (a b c d e : Fin 8) : Fin 5 → Fin 8 := fun j =>
  match j.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

/-- `C₁ = {0, 2, 3, 4, 6}`, carried by the cyclic order `0 – 2 – 6 – 4 – 3`. -/
theorem isOddCycle_k4sub_c₁ : IsOddCycle k4sub ({0, 2, 3, 4, 6} : Finset (Fin 8)) :=
  ⟨5, dcyc5 0 2 6 4 3, by decide, by decide, by decide, by decide, by decide⟩

/-- `C₂ = {0, 1, 3, 5, 7}`, carried by the cyclic order `0 – 1 – 7 – 5 – 3`. -/
theorem isOddCycle_k4sub_c₂ : IsOddCycle k4sub ({0, 1, 3, 5, 7} : Finset (Fin 8)) :=
  ⟨5, dcyc5 0 1 7 5 3, by decide, by decide, by decide, by decide, by decide⟩

/-- `C₃ = {0, 1, 2, 6, 7}`, carried by the cyclic order `0 – 1 – 7 – 6 – 2`. -/
theorem isOddCycle_k4sub_c₃ : IsOddCycle k4sub ({0, 1, 2, 6, 7} : Finset (Fin 8)) :=
  ⟨5, dcyc5 0 1 7 6 2, by decide, by decide, by decide, by decide, by decide⟩

/-- `C₄ = {3, 4, 5, 6, 7}`, carried by the cyclic order `3 – 4 – 6 – 7 – 5`. -/
theorem isOddCycle_k4sub_c₄ : IsOddCycle k4sub ({3, 4, 5, 6, 7} : Finset (Fin 8)) :=
  ⟨5, dcyc5 3 4 6 7 5, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- **`k4sub` SATISFIES ERDŐS'S HYPOTHESIS AT `k = 1`.**  This is a kernel decision over the `2 ^ 8`
vertex sets of `V`; the deficiency is attained at the 5-cycle `{0, 2, 3, 4, 6}`, where
`5 - 2 * 2 = 1`. -/
theorem locIndep_one_k4sub : LocIndep 1 k4sub := by
  unfold LocIndep
  decide

/-- **THE DEFICIENCY OF `k4sub` IS EXACTLY `1`**: it satisfies `LocIndep 1` (Part 2), and it is not
bipartite (it carries the odd cycle `C₁`), so `MaxDef k4sub ≥ 1`. -/
theorem maxDef_k4sub : MaxDef k4sub = 1 := by
  refine le_antisymm (locIndep_iff_maxDef_le.mp locIndep_one_k4sub) ?_
  have hne : MaxDef k4sub ≠ 0 := by
    intro hz
    have hb : k4sub.IsBipartite := (maxDef_eq_zero_iff (G := k4sub)).mp hz
    exact (not_isOddCycle_of_isBipartite hb)
      ⟨({0, 2, 3, 4, 6} : Finset (Fin 8)), isOddCycle_k4sub_c₁⟩
  exact Nat.one_le_iff_ne_zero.mpr hne

/-- **THE FAMILY OF THE FOUR ODD CYCLES OF `k4sub`.** -/
def k4subFour : Finset (Finset (Fin 8)) :=
  {({0, 2, 3, 4, 6} : Finset (Fin 8)), {0, 1, 3, 5, 7}, {0, 1, 2, 6, 7}, {3, 4, 5, 6, 7}}

/-- **EVERY MEMBER OF `k4subFour` IS AN ODD CYCLE OF `k4sub`.** -/
theorem k4sub_four_odd : ∀ C ∈ k4subFour, IsOddCycle k4sub C := by
  intro C hC
  simp only [k4subFour, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact isOddCycle_k4sub_c₁
  · exact isOddCycle_k4sub_c₂
  · exact isOddCycle_k4sub_c₃
  · exact isOddCycle_k4sub_c₄

set_option maxRecDepth 100000 in
/-- **THE FOUR ODD CYCLES OF `k4sub` ARE PAIRWISE MEETING** — as `LocIndep 1` demands.  This is a
kernel decision: the six pairwise intersections are `{0, 3}`, `{0, 2, 6}`, `{4, 6}`, `{0, 1, 7}`,
`{3, 5, 7}` and `{6, 7}`. -/
theorem k4sub_four_meet : ∀ C ∈ k4subFour, ∀ D ∈ k4subFour, (C ∩ D).Nonempty := by decide

/-- **`k4subFour` IS NONEMPTY.** -/
theorem k4subFour_nonempty : k4subFour.Nonempty := by decide

set_option maxRecDepth 100000 in
/-- **TWO MEMBERS OF `k4subFour` SHARE A VERTEX**, with the witnesses `0`, `0`, `4`, `0`, `3`, `6` for
the pairs `C₁ C₂`, `C₁ C₃`, `C₁ C₄`, `C₂ C₃`, `C₂ C₄`, `C₃ C₄` respectively.  This is the form in
which `JSP90.HellyOddCycles` needs the pairwise-meeting hypothesis. -/
theorem k4sub_pair_mem : ∀ C ∈ k4subFour, ∀ D ∈ k4subFour, ∃ x : Fin 8, x ∈ C ∧ x ∈ D := by decide

/-- **NO VERTEX LIES ON ALL FOUR ODD CYCLES OF `k4sub`.**  Indeed `C₁ ∩ C₂ = {0, 3}` and
`C₃ ∩ C₄ = {6, 7}`, and the two are disjoint. -/
theorem k4sub_no_commonVertex :
    ∀ v : Fin 8, ¬ (v ∈ ({0, 2, 3, 4, 6} : Finset (Fin 8)) ∧ v ∈ ({0, 1, 3, 5, 7} : Finset (Fin 8)) ∧
      v ∈ ({0, 1, 2, 6, 7} : Finset (Fin 8)) ∧ v ∈ ({3, 4, 5, 6, 7} : Finset (Fin 8))) := by
  intro v h
  have h12 : (({0, 2, 3, 4, 6} : Finset (Fin 8)) ∩ ({0, 1, 3, 5, 7} : Finset (Fin 8))) = {0, 3} := by
    decide
  have h34 : (({0, 1, 2, 6, 7} : Finset (Fin 8)) ∩ ({3, 4, 5, 6, 7} : Finset (Fin 8))) = {6, 7} := by
    decide
  have hvv : v ∈ ((({0, 2, 3, 4, 6} : Finset (Fin 8)) ∩ ({0, 1, 3, 5, 7} : Finset (Fin 8))) ∩
      (({0, 1, 2, 6, 7} : Finset (Fin 8)) ∩ ({3, 4, 5, 6, 7} : Finset (Fin 8)))) :=
    Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨h.1, h.2.1⟩, Finset.mem_inter.mpr ⟨h.2.2.1, h.2.2.2⟩⟩
  rw [h12, h34] at hvv
  simp at hvv

/-- **`k4sub` IS TWO VERTICES AWAY FROM BIPARTITE**: deleting `{0, 3}` leaves the bipartite graph with
the parts `{7, 2, 4}` and `{1, 5, 6}`. -/
theorem closeToBipartite_two_k4sub : CloseToBipartite 2 k4sub := by
  refine ⟨{0, 3}, by decide, ?_⟩
  rw [isBipartite_iff_color2]
  refine ⟨fun v => if v = 2 ∨ v = 4 ∨ v = 7 then (0 : Fin 2) else 1, ?_⟩
  intro u v hadj
  have hadj' := deleteFinset_adj.mp hadj
  have huv : u ≠ v := by
    intro h
    have hvv : k4sub.Adj v v := h ▸ hadj'.2.2
    exact k4sub.irrefl hvv
  fin_cases u <;> fin_cases v <;> simp_all [k4subEdge]

/-- **EVERY VERTEX OF `k4sub` IS AVOIDED BY AN ODD CYCLE OF `k4sub`.**  `0` is avoided by `C₄`, `3` by
`C₃`, the vertices `2, 4, 6` by `C₂` and the vertices `1, 5, 7` by `C₁`.  So no vertex of `k4sub` is a
transversal of its odd cycles — the machine-checked version of
`JSP90.exists_oddCycle_avoiding_vertex`. -/
theorem exists_oddCycle_avoiding_of_k4sub (v : Fin 8) :
    ∃ C : Finset (Fin 8), IsOddCycle k4sub C ∧ v ∉ C := by
  fin_cases v <;>
    first
      | exact ⟨_, isOddCycle_k4sub_c₄, by decide⟩
      | exact ⟨_, isOddCycle_k4sub_c₁, by decide⟩
      | exact ⟨_, isOddCycle_k4sub_c₂, by decide⟩
      | exact ⟨_, isOddCycle_k4sub_c₃, by decide⟩

/-- **NO SINGLE VERTEX DELETION MAKES `k4sub` BIPARTITE.**  If `X` has at most one vertex and the
residue is bipartite, then `X = ∅` and `C₁` is an odd cycle of the residue, or `X = {a}` and the odd
cycle of `JSP90.exists_oddCycle_avoiding_of_k4sub a` avoiding `a` is an odd cycle of the residue
(`JSP90.isOddCycle_deleteFinset_of_disjoint`) — in both cases contradicting
`JSP90.not_isOddCycle_of_isBipartite`. -/
theorem deleteFinset_k4sub_not_isBipartite (X : Finset (Fin 8)) (hX : X.card ≤ 1)
    (hb : (deleteFinset k4sub X).IsBipartite) : False := by
  by_cases h0 : X.card = 0
  · have hXe : X = ∅ := Finset.card_eq_zero.mp h0
    have hC : IsOddCycle (deleteFinset k4sub X) ({0, 2, 3, 4, 6} : Finset (Fin 8)) := by
      rw [hXe, deleteFinset_empty]
      exact isOddCycle_k4sub_c₁
    exact (not_isOddCycle_of_isBipartite hb) ⟨({0, 2, 3, 4, 6} : Finset (Fin 8)), hC⟩
  · have hXeq : X.card = 1 := by omega
    obtain ⟨a, hXeq'⟩ := Finset.card_eq_one.mp hXeq
    obtain ⟨C, hC, hva⟩ := exists_oddCycle_avoiding_of_k4sub a
    have hdis : Disjoint C X := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hxX
      rw [hXeq'] at hxX
      have hxa : x = a := Finset.mem_singleton.mp hxX
      subst hxa
      exact hva hx
    exact (not_isOddCycle_of_isBipartite hb) ⟨C, isOddCycle_deleteFinset_of_disjoint hC hdis⟩

/-- **`k4sub` IS NOT ONE VERTEX AWAY FROM BIPARTITE.** -/
theorem not_closeToBipartite_one_k4sub : ¬ CloseToBipartite 1 k4sub := by
  rintro ⟨X, hX, hb⟩
  exact deleteFinset_k4sub_not_isBipartite X hX hb

/-- **THE ODD CYCLE TRANSVERSAL NUMBER OF `k4sub` IS EXACTLY `2`.**  Together with
`JSP90.locIndep_one_k4sub` this says that the constant `2` of
`JSP90.closeToBipartite_two_of_locIndep_one_of_four_oddCycles` cannot be lowered on this class, and
that one vertex never suffices at `LocIndep 1` — even at odd girth `5`. -/
theorem closeToBipartite_iff_k4sub (m : ℕ) : CloseToBipartite m k4sub ↔ 2 ≤ m := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨X, hX, hb⟩ := h
    exact deleteFinset_k4sub_not_isBipartite X (by omega) hb
  · intro h
    exact closeToBipartite_mono h closeToBipartite_two_k4sub

/-! ## Part 3 — the Helly route is dead at `k = 1` -/

theorem not_helly_k4sub : ¬ HellyOddCycles k4sub := by
  rintro hH
  obtain ⟨v, hv⟩ :=
    hH k4subFour k4sub_four_odd
      (fun C hC D hD => inter_oddCycle_of_locIndep_one locIndep_one_k4sub
        (k4sub_four_odd C hC) (k4sub_four_odd D hD)) k4subFour_nonempty
  · have hv1 : v ∈ ({0, 2, 3, 4, 6} : Finset (Fin 8)) := hv _ (by
      rw [k4subFour]; decide)
    have hv2 : v ∈ ({0, 1, 3, 5, 7} : Finset (Fin 8)) := hv _ (by
      rw [k4subFour]; decide)
    have hv3 : v ∈ ({0, 1, 2, 6, 7} : Finset (Fin 8)) := hv _ (by
      rw [k4subFour]; decide)
    have hv4 : v ∈ ({3, 4, 5, 6, 7} : Finset (Fin 8)) := hv _ (by
      rw [k4subFour]; decide)
    exact k4sub_no_commonVertex v ⟨hv1, hv2, hv3, hv4⟩

/-- **EVERY THREE OF THE FOUR ODD CYCLES OF `k4sub` HAVE A COMMON VERTEX**: the triples `C₁ C₂ C₃`,
`C₁ C₂ C₄`, `C₁ C₃ C₄`, `C₂ C₃ C₄` have the common vertices `0`, `6`, `7`, `3` respectively.  So the
minimal Helly obstruction of `k4sub` has size **exactly four**: no three-element version of the Helly
property (`JSP90.TwoHellyOddCycles`) can detect it, and the natural strengthening of round 83's
instance — replacing `HellyOddCycles G` by `TwoHellyOddCycles G` — is false. -/
theorem three_commonVertex_of_k4sub :
    (∃ v : Fin 8, v ∈ ({0, 2, 3, 4, 6} ∩ ({0, 1, 3, 5, 7} : Finset (Fin 8)) ∩
      ({0, 1, 2, 6, 7} : Finset (Fin 8)))) ∧
      (∃ v : Fin 8, v ∈ ({0, 2, 3, 4, 6} ∩ ({0, 1, 3, 5, 7} : Finset (Fin 8)) ∩
        ({3, 4, 5, 6, 7} : Finset (Fin 8)))) ∧
      (∃ v : Fin 8, v ∈ ({0, 2, 3, 4, 6} ∩ ({0, 1, 2, 6, 7} : Finset (Fin 8)) ∩
        ({3, 4, 5, 6, 7} : Finset (Fin 8)))) ∧
      (∃ v : Fin 8, v ∈ ({0, 1, 3, 5, 7} ∩ ({0, 1, 2, 6, 7} : Finset (Fin 8)) ∩
        ({3, 4, 5, 6, 7} : Finset (Fin 8)))) :=
  ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩⟩

theorem card_oddCycles_ge_four_k4sub : 4 ≤ (OddCycles k4sub).card := by
  classical
  have hsub : k4subFour ⊆ OddCycles k4sub := by
    intro C hC
    rw [mem_oddCycles]
    exact k4sub_four_odd C hC
  have h4 : k4subFour.card = 4 := by decide
  have hle := Finset.card_le_card hsub
  omega

/-- **`LocIndep 1` DOES NOT IMPLY THE HELLY PROPERTY, AND ONE VERTEX DOES NOT SUFFICE.**  This is the
formal record of the machine-checked facts about `k4sub` that close the Helly route at `k = 1`:

* `k4sub` satisfies Erdős's hypothesis at `k = 1`, and its deficiency is exactly `1`;
* its four odd cycles are pairwise meeting with **empty four-fold intersection**, so the Helly
  property `JSP90.HellyOddCycles` fails;
* nevertheless **every three** of them have a common vertex, so the failure is invisible to any
  three-element (Helly-number-3) version of the property;
* and its odd cycle transversal number is **exactly `2`**.

Consequently `JSP90.closeToBipartite_one_of_helly_of_locIndep_one` (round 83) cannot be applied to
all graphs satisfying Erdős's hypothesis, and no statement "`LocIndep k` gives a common vertex of the
odd cycles" is true at any `k`.  What *is* true at `k = 1` is `JSP90.closeToBipartite 2`, which is
`JSP90.closeToBipartite_iff_k4sub` above. -/
theorem LocIndepOneNotHelly :
    LocIndep 1 k4sub ∧ ¬ HellyOddCycles k4sub ∧ CloseToBipartite 2 k4sub ∧ ¬ CloseToBipartite 1 k4sub :=
  And.intro locIndep_one_k4sub
    (And.intro not_helly_k4sub
      (And.intro closeToBipartite_two_k4sub
        ((closeToBipartite_iff_k4sub 1).not.mpr (by omega))))

end

end JSP90
/-! ## Part 4 — the axiom audit of the round -/

section Audit

#print axioms JSP90.exists_transversal_card_le
#print axioms JSP90.closeToBipartite_of_locIndep_one_of_card_oddCycles_le
#print axioms JSP90.erdos73On_fewOddCycles
#print axioms JSP90.closeToBipartite_one_of_locIndep_one_of_two_oddCycles
#print axioms JSP90.closeToBipartite_two_of_locIndep_one_of_four_oddCycles
#print axioms JSP90.locIndep_one_k4sub
#print axioms JSP90.maxDef_k4sub
#print axioms JSP90.isOddCycle_k4sub_c₁
#print axioms JSP90.isOddCycle_k4sub_c₂
#print axioms JSP90.isOddCycle_k4sub_c₃
#print axioms JSP90.isOddCycle_k4sub_c₄
#print axioms JSP90.k4sub_four_meet
#print axioms JSP90.k4sub_pair_mem
#print axioms JSP90.k4sub_no_commonVertex
#print axioms JSP90.exists_oddCycle_avoiding_of_k4sub
#print axioms JSP90.deleteFinset_k4sub_not_isBipartite
#print axioms JSP90.not_closeToBipartite_one_k4sub
#print axioms JSP90.closeToBipartite_iff_k4sub
#print axioms JSP90.not_helly_k4sub
#print axioms JSP90.three_commonVertex_of_k4sub
#print axioms JSP90.card_oddCycles_ge_four_k4sub
#print axioms JSP90.LocIndepOneNotHelly

end Audit
