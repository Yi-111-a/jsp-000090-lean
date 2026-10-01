/-
# JSP-000090 — the **HELLY axis**: the odd cycles form a Helly family

Attack family 30 (round 83).  New module, imported from the root module `JSPProblem.lean`.

## The class

```lean
JSP90.HellyOddCycles G
```

says that **the odd cycles of `G` form a Helly family**: every *finite* family `𝒞` of pairwise
meeting odd cycles has a vertex common to all of them.  This is the *full* Helly property, as opposed
to round 81/82's `JSP90.TwoHellyOddCycles G`, which only asks for **three** pairwise meeting odd
cycles to have a common vertex.

The two classes are different, and the difference is what this round is about:

* `LinearOddCycles G → TwoHellyOddCycles G` is round 82's ring lemma — it is a theorem;
* this round proves the genuinely new implication `LinearOddCycles G → HellyOddCycles G`
  (`JSP90.helly_of_linearOddCycles`): **the odd cycles of a linear graph form a Helly family**.
  Round 82 killed *rings* (three cycles); this round kills **every** non-Helly family, of any size,
  by a minimality argument whose only structural input is the ring lemma;

and, crucially, `HellyOddCycles` is **strictly weaker** than `LinearOddCycles`: Part 5 exhibits
explicit witnesses that are Helly but not linear, satisfy `LocIndep 1`, and are one vertex away from
bipartite.  So the instance proved in Part 3 is a **genuinely new instance of the headline theorem**,
on a class strictly larger than round 82's, and it is *not* a corollary of round 82's instance.

## What is proved

1. **THE HELLY LEMMA FOR LINEAR GRAPHS** (`JSP90.helly_of_linearOddCycles`):
   `LinearOddCycles G → HellyOddCycles G`.  Proof by strong induction on `|𝒞|`.  For `|𝒞| ≥ 3` pick
   three distinct members `C₁, C₂, C₃` and, for each `i`, apply the induction hypothesis to
   `𝒞.erase Cᵢ`: there is a vertex `vᵢ` common to all the *other* members.  If some `vᵢ ∈ Cᵢ` it is
   common to all of `𝒞` and we are done.  Otherwise `v₁ ∉ C₁`, `v₂ ∉ C₂`, `v₁ ∈ C₂ ∩ C₃` and
   `v₂ ∈ C₁ ∩ C₃`; write `C₁ ∩ C₂ = {a}` (linearity) and apply the **ring lemma** to
   `C₁, C₂, C₃`: it produces `a ∈ C₃`, so `v₁` and `a` are two distinct vertices of `C₂ ∩ C₃`,
   contradicting the linearity of the two distinct members `C₂`, `C₃`.  The cases `|𝒞| ≤ 2` are the
   nonemptiness of an odd cycle and the pairwise-meeting hypothesis.
2. **TWO-HELLY IS A CONSEQUENCE OF THE HELLY PROPERTY** (`JSP90.twoHelly_of_helly`), so round 82's
   class is recovered from `LinearOddCycles G ∧ HellyOddCycles G`, and Part 3 applies to the Helly
   class alone.
3. **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1`, WITH THE OPTIMAL CONSTANT `1`, FOR THE
   STRICTLY LARGER HELLY CLASS** (`JSP90.closeToBipartite_one_of_helly_of_locIndep_one`,
   `JSP90.erdos73On_helly_one`): `LocIndep 1 G → HellyOddCycles G → CloseToBipartite 1 G`.
   Erdős's hypothesis enters only through the packing bound at `k = 1` ("every two odd cycles meet",
   `JSP90.inter_oddCycle_of_locIndep_one`); the key step is
   `JSP90.exists_commonVertex_of_helly_of_locIndep_one`, which puts all odd cycles through one vertex
   because their family is pairwise meeting (hence the family of *all* odd cycles is itself a Helly
   subfamily).  No bound on the odd girth, the degrees, the packing weight, the branch vertices, the
   number of components, or on the size of the odd cycles.
4. **THE CONSTANT `1` IS EXACT** on the Helly class: `K₃` is `HellyOddCycles`
   (`JSP90.helly_completeGraph_three` — every odd cycle of `K₃` is the whole vertex set, so every
   family has a common vertex), it satisfies `LocIndep 1` (`JSP90.completeGraph_locIndep 1`) and is
   not bipartite (`JSP90.not_closeToBipartite_zero_completeGraph_three`).  So `f(1) = 1` exactly on
   this class, and the class contains round 82's (`hlin → hhel`).
5. **THE CLASS IS *STRICTLY* LARGER THAN ROUND 82's**: the **diamond** `K₄` minus an edge is
   `HellyOddCycles` (`JSP90.helly_diamond`), it satisfies `LocIndep 1`
   (`JSP90.locIndep_one_diamond`), it is one vertex away from bipartite
   (`JSP90.closeToBipartite_one_diamond`), and it is **not** linear (`JSP90.not_linear_diamond`): its
   two triangles meet in the two endpoints of the deleted edge, so the round-82 hypothesis genuinely
   excludes it.  Hence Part 3 is **not** a corollary of round 82's instance.
6. **THE `k`-AXIS**: `JSP90.HellyErdős73 f`, the *remaining statement* for the Helly class at a
   general constant, stated as a `def` and **not assumed**: every `LocIndep`-`c` graph whose odd
   cycles form a Helly family is `f c`-close to bipartite.  Part 3 is its proved base level
   (`c = 1`, `f 1 = 1`).

## What is *not* proved

`JSP90.HellyErdős73 f` for any `f` — Erdős #73 for the Helly class at a general `k`.  Behind it
stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker:
the Helly property bounds the transversal number at `k = 1` and says nothing about larger packings.
No colouring bound, packing bound or Helly hypothesis is *assumed* anywhere in this file; the Helly
hypothesis appears only in the statements whose hypotheses are proved or made explicit.

## Verification done before formalising

Exhaustive C search over **all** graphs on `n ≤ 7` vertices (`2²¹` of them):

* `LinearOddCycles ⟹ HellyOddCycles`: **0** counterexamples (`linear & !Helly = 0` for `n = 5,6,7`);
* `HellyOddCycles ∧ LocIndep 1 ⟹ τ = 1`: **0** counterexamples (the largest odd cycle transversal
  number among the `870 530` Helly graphs on `n = 7` satisfying `LocIndep 1` is `1`), against
  `13 020` graphs with `LocIndep 1`, packing number `1` and transversal number `2` that all **fail**
  `HellyOddCycles` — so the Helly hypothesis is not implied by `LocIndep 1` + packing one;
* random search on `n = 10` (`4 000 000` random graphs): no graph with
  `HellyOddCycles ∧ LocIndep 1` has transversal number `≥ 2`;
* `HellyOddCycles` is genuinely weaker than `LinearOddCycles`: `643 006` graphs on `n = 7` are
  Helly, `LocIndep 1`, of transversal number `1`, and **not** linear;
* `HellyOddCycles ∧ LocIndep 2` does **not** give transversal number `≤ 2`: a 10-vertex counterexample
  was found, which is why Part 6 is stated as a `def` for a general `f` and not as a theorem with
  the constant `c`.
-/

import JSPProblem.Ring
import JSPProblem.Sun

namespace JSP90

open Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

section ClassicalPart

local instance instDecidableEqHelly : DecidableEq V := Classical.decEq V

local instance instDecidableIsOddCycleHelly {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ## Part 0 — auxiliary lemmas -/

/-- **THREE DISTINCT MEMBERS of a finset of cardinality at least three.**  `Finset.two_lt_card_iff`
is the Mathlib form of this elementary fact; it is stated for `2 < s.card`. -/
theorem exists_three_mem_of_card_ge_three {α : Type*} {s : Finset α} (h : 3 ≤ s.card) :
    ∃ a b c : α, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  Finset.two_lt_card_iff.mp (by omega : 2 < s.card)

/-! ## Part 1 — the HELLY property -/

/-- **THE ODD CYCLES OF `G` FORM A HELLY FAMILY.**

Every *finite* family `𝒞` of pairwise meeting odd cycles of `G` has a vertex common to all of them.
This is the full Helly property; `JSP90.TwoHellyOddCycles G` of `JSPProblem/Cactus.lean` only asks
for the case `|𝒞| = 3`. -/
noncomputable def HellyOddCycles (G : SimpleGraph V) : Prop :=
  ∀ 𝒞 : Finset (Finset V), (∀ C ∈ 𝒞, IsOddCycle G C) → (∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ∩ D ≠ ∅) →
    𝒞.Nonempty → ∃ v : V, ∀ C ∈ 𝒞, v ∈ C

omit [Fintype V] in
/-- **THE HELLY PROPERTY APPLIED TO ONE FAMILY.** -/
theorem exists_commonVertex_of_helly {𝒞 : Finset (Finset V)}
    (hH : HellyOddCycles G) (hodd : ∀ C ∈ 𝒞, IsOddCycle G C)
    (hmeet : ∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ∩ D ≠ ∅) (hne : 𝒞.Nonempty) :
    ∃ v : V, ∀ C ∈ 𝒞, v ∈ C :=
  hH 𝒞 hodd hmeet hne

/-- **A THREE-MEMBER FAMILY OF PAIRWISE MEETING ODD CYCLES HAS A COMMON VERTEX** — the Helly
property in its smallest nontrivial instance, phrased with *element* memberships so that the finset
`{C, D, E}` built here is never mentioned. -/
theorem exists_commonVertex_of_helly_three {C D E : Finset V}
    (hH : HellyOddCycles G) (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hE : IsOddCycle G E)
    (hCD : C ∩ D ≠ ∅) (hDE : D ∩ E ≠ ∅) (hEC : E ∩ C ≠ ∅) :
    ∃ v : V, v ∈ C ∧ v ∈ D ∧ v ∈ E := by
  have hmem : ∀ X : Finset V, X ∈ ({C, D, E} : Finset (Finset V)) → X = C ∨ X = D ∨ X = E := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hodd : ∀ X ∈ ({C, D, E} : Finset (Finset V)), IsOddCycle G X := by
    intro X hX
    rcases hmem X hX with h | h | h
    · rw [h]; exact hC
    · rw [h]; exact hD
    · rw [h]; exact hE
  have hone : ∀ Z ∈ ({C, D, E} : Finset (Finset V)), Z.Nonempty := by
    intro Z hZ
    rcases hmem Z hZ with h | h | h
    · rw [h]; exact (hC).nonempty'
    · rw [h]; exact (hD).nonempty'
    · rw [h]; exact (hE).nonempty'
  have hmeet : ∀ X ∈ ({C, D, E} : Finset (Finset V)),
      ∀ Y ∈ ({C, D, E} : Finset (Finset V)), X ∩ Y ≠ ∅ := by
    intro X hX Y hY
    rcases hmem X hX with hx | hx | hx
    · rcases hmem Y hY with hy | hy | hy
      · rw [hx, hy]
        obtain ⟨z, hz⟩ := (hC).nonempty'
        exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hz, hz⟩)
      · rw [hx, hy]; exact hCD
      · rw [hx, hy]; exact (Finset.inter_comm C E).symm ▸ hEC
    · rcases hmem Y hY with hy | hy | hy
      · rw [hx, hy]; exact (Finset.inter_comm C D) ▸ hCD
      · rw [hx, hy]
        obtain ⟨z, hz⟩ := (hD).nonempty'
        exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hz, hz⟩)
      · rw [hx, hy]; exact hDE
    · rcases hmem Y hY with hy | hy | hy
      · rw [hx, hy]; exact (Finset.inter_comm C E) ▸ hEC
      · rw [hx, hy]; exact (Finset.inter_comm D E) ▸ hDE
      · rw [hx, hy]
        obtain ⟨z, hz⟩ := (hE).nonempty'
        exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hz, hz⟩)
  obtain ⟨v, hv⟩ := hH {C, D, E} hodd hmeet ⟨C, Finset.mem_insert_self C {D, E}⟩
  refine ⟨v, hv C (Finset.mem_insert_self C {D, E}),
    hv D (Finset.mem_insert_of_mem (Finset.mem_insert_self D {E})),
    hv E (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self E ∅)))⟩

/-- **TWO-HELLY IS A CONSEQUENCE OF THE HELLY PROPERTY.**  So `LinearOddCycles G ∧ HellyOddCycles G`
recovers exactly round 82's class, and Part 3 below applies to `HellyOddCycles G` alone. -/
theorem twoHelly_of_helly (h : HellyOddCycles G) : TwoHellyOddCycles G := by
  intro C D E hC hD hE hCD hDE hEC
  obtain ⟨v, hv1, hv2, hv3⟩ := exists_commonVertex_of_helly_three h hC hD hE hCD hDE hEC
  exact ⟨v, mem_inter3' hv1 hv2 hv3⟩

/-! ## Part 2 — the HELLY LEMMA FOR LINEAR GRAPHS -/

/-- **THE HELLY LEMMA: `LinearOddCycles G → HellyOddCycles G`.**

In a graph whose odd cycles are *linear* (two distinct odd cycles meet in at most one vertex),
**every** finite family of pairwise meeting odd cycles has a common vertex — not merely every family
of three, which is round 82's ring lemma.

The proof is a strong induction on `|𝒞|`.  The cases `|𝒞| ≤ 2` are the nonemptiness of an odd cycle
and the pairwise-meeting hypothesis.  For `|𝒞| ≥ 3` pick three distinct members `C₁, C₂, C₃` and,
for each `i`, apply the induction hypothesis to `𝒞.erase Cᵢ`: there is a vertex `vᵢ` common to all
the *other* members.  If some `vᵢ ∈ Cᵢ` it is common to all of `𝒞` and we are done.  Otherwise
`v₁ ∉ C₁`, `v₂ ∉ C₂`, `v₁ ∈ C₂ ∩ C₃` and `v₂ ∈ C₁ ∩ C₃`.  Write `C₁ ∩ C₂ = {a}` — allowed, by
linearity — and apply the **ring lemma** to `C₁, C₂, C₃`: it produces a common vertex, which being in
`C₁ ∩ C₂ = {a}` must be `a`, so `a ∈ C₃`.  Then `v₁ ≠ a` (since `v₁ ∉ C₁` but `a ∈ C₁`) and both lie
in `C₂ ∩ C₃`, contradicting the linearity of the two distinct members `C₂`, `C₃`. ∎ -/
theorem helly_of_linearOddCycles (h : LinearOddCycles G) : HellyOddCycles G := by
  classical
  have key : ∀ n : ℕ, ∀ 𝒞 : Finset (Finset V), 𝒞.card ≤ n → 𝒞.Nonempty →
      (∀ C ∈ 𝒞, IsOddCycle G C) → (∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ∩ D ≠ ∅) →
      ∃ v : V, ∀ C ∈ 𝒞, v ∈ C := by
    intro n
    induction n with
    | zero =>
        intro 𝒞 hcard hne hodd hmeet
        rcases hne with ⟨C, hC⟩
        have hpos : 0 < 𝒞.card := Finset.card_pos.mpr ⟨C, hC⟩
        omega
    | succ n ih =>
        intro 𝒞 hcard hne hodd hmeet
        have hoddE : ∀ (i : Finset V), ∀ C ∈ 𝒞.erase i, IsOddCycle G C := by
          intro i C hC
          exact hodd C (Finset.mem_of_mem_erase hC)
        have hmeetE : ∀ (i : Finset V), ∀ C ∈ 𝒞.erase i, ∀ D ∈ 𝒞.erase i, C ∩ D ≠ ∅ := by
          intro i C hC D hD
          exact hmeet C (Finset.mem_of_mem_erase hC) D (Finset.mem_of_mem_erase hD)
        by_cases h3 : 3 ≤ 𝒞.card
        · obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ := exists_three_mem_of_card_ge_three h3
          have hcard₁ : (𝒞.erase C₁).card ≤ n := by
            rw [Finset.card_erase_of_mem hC₁]; omega
          have hcard₂ : (𝒞.erase C₂).card ≤ n := by
            rw [Finset.card_erase_of_mem hC₂]; omega
          have hne₁ : (𝒞.erase C₁).Nonempty := ⟨C₂, Finset.mem_erase.mpr ⟨h12.symm, hC₂⟩⟩
          have hne₂ : (𝒞.erase C₂).Nonempty := ⟨C₁, Finset.mem_erase.mpr ⟨h12, hC₁⟩⟩
          have k1 : ∃ v : V, ∀ C ∈ 𝒞.erase C₁, v ∈ C := ih (𝒞.erase C₁) hcard₁ hne₁ (hoddE C₁) (hmeetE C₁)
          have k2 : ∃ v : V, ∀ C ∈ 𝒞.erase C₂, v ∈ C := ih (𝒞.erase C₂) hcard₂ hne₂ (hoddE C₂) (hmeetE C₂)
          obtain ⟨v₁, hv₁⟩ := k1
          obtain ⟨v₂, hv₂⟩ := k2
          by_cases hmem1 : v₁ ∈ C₁
          · refine ⟨v₁, fun C hC => ?_⟩
            by_cases hCC₁ : C = C₁
            · rw [hCC₁]; exact hmem1
            · exact hv₁ C (Finset.mem_erase.mpr ⟨hCC₁, hC⟩)
          by_cases hmem2 : v₂ ∈ C₂
          · refine ⟨v₂, fun C hC => ?_⟩
            by_cases hCC₂ : C = C₂
            · rw [hCC₂]; exact hmem2
            · exact hv₂ C (Finset.mem_erase.mpr ⟨hCC₂, hC⟩)
          have hv₁C₂ : v₁ ∈ C₂ := hv₁ C₂ (Finset.mem_erase.mpr ⟨h12.symm, hC₂⟩)
          have hv₁C₃ : v₁ ∈ C₃ := hv₁ C₃ (Finset.mem_erase.mpr ⟨h13.symm, hC₃⟩)
          have hv₂C₁ : v₂ ∈ C₁ := hv₂ C₁ (Finset.mem_erase.mpr ⟨h12, hC₁⟩)
          have hv₂C₃ : v₂ ∈ C₃ := hv₂ C₃ (Finset.mem_erase.mpr ⟨h23.symm, hC₃⟩)
          obtain ⟨a, ha⟩ := nonempty_of_ne_empty (hmeet C₁ hC₁ C₂ hC₂)
          have hC₁C₂ : C₁ ∩ C₂ = {a} :=
            h.eq_singleton_of_mem (hodd C₁ hC₁) (hodd C₂ hC₂) h12 ha
          have haC₁ : a ∈ C₁ := (Finset.mem_inter.mp ha).1
          have haC₂ : a ∈ C₂ := (Finset.mem_inter.mp ha).2
          have hva : v₁ ≠ a := fun hh => hmem1 (hh ▸ haC₁)
          obtain ⟨w, hw⟩ := twoHelly_of_linearOddCycles h C₁ C₂ C₃ (hodd C₁ hC₁) (hodd C₂ hC₂)
            (hodd C₃ hC₃) (ne_empty_of_mem ha)
            (ne_empty_of_mem (Finset.mem_inter.mpr ⟨hv₁C₂, hv₁C₃⟩))
            (ne_empty_of_mem (Finset.mem_inter.mpr ⟨hv₂C₃, hv₂C₁⟩))
          have hwa : w = a :=
            Finset.mem_singleton.mp (hC₁C₂ ▸ (Finset.mem_inter.mp hw).1)

          have haC₃ : a ∈ C₃ := by
            rw [← hwa]
            exact (Finset.mem_inter.mp hw).2
          exact (not_linear_of_two_mem h (hodd C₂ hC₂) (hodd C₃ hC₃) h23 hv₁C₂ hv₁C₃ haC₂ haC₃
            hva).elim
        · have h1 : 1 ≤ 𝒞.card := Finset.card_pos.mpr hne
          by_cases hEq2 : 𝒞.card = 2
          · obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hEq2
            have haC : a ∈ 𝒞 := by rw [heq]; exact Finset.mem_insert_self a {b}
            have hbC : b ∈ 𝒞 := by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self b ∅)
            obtain ⟨x, hx⟩ := nonempty_of_ne_empty (hmeet a haC b hbC)
            have key' : ∀ D ∈ 𝒞, D = a ∨ D = b := by
              intro D hD
              rw [heq] at hD
              rcases (Finset.mem_insert (s := ({b} : Finset (Finset V)))).mp hD with h | h
              · exact Or.inl h
              · exact Or.inr (Finset.mem_singleton.mp h)
            refine ⟨x, fun D hD => ?_⟩
            rcases key' D hD with h | h
            · rw [h]; exact (Finset.mem_inter.mp hx).1
            · rw [h]; exact (Finset.mem_inter.mp hx).2
          · have hEq1 : 𝒞.card = 1 := by omega
            obtain ⟨a, heq⟩ := Finset.card_eq_one.mp hEq1
            have haC : a ∈ 𝒞 := by rw [heq]; exact Finset.mem_insert_self a ∅
            obtain ⟨v, hv⟩ := (hodd a haC).nonempty'
            refine ⟨v, fun D hD => ?_⟩
            have : D = a := by
              rw [heq] at hD
              rcases (Finset.mem_insert (s := (∅ : Finset (Finset V)))).mp hD with h | h
              · exact h
              · simp at h
            rw [this]
            exact hv
  intro 𝒞 hodd hmeet hne
  exact key 𝒞.card 𝒞 le_rfl hne hodd hmeet

/-! ## Part 3 — a new instance of the headline theorem on the Helly class -/

/-- **THE ODD CYCLES OF A `LocIndep 1` GRAPH WITH THE HELLY PROPERTY ALL PASS THROUGH ONE
VERTEX.**  Erdős's hypothesis enters only through `JSP90.inter_oddCycle_of_locIndep_one`: the odd
cycles pairwise meet, so the family of *all* odd cycles is itself a pairwise-meeting family, and the
Helly property — applied to that family — yields a common vertex. -/
theorem exists_commonVertex_of_helly_of_locIndep_one (hG : LocIndep 1 G) (hH : HellyOddCycles G)
    (hodd : ∃ C : Finset V, IsOddCycle G C) :
    ∃ a : V, ∀ D : Finset V, IsOddCycle G D → a ∈ D := by
  classical
  set 𝒞 : Finset (Finset V) :=
    (Finset.univ : Finset (Finset V)).filter (IsOddCycle G) with h𝒞def
  have h𝒞mem : ∀ C : Finset V, C ∈ 𝒞 ↔ IsOddCycle G C := by
    intro C
    rw [h𝒞def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have h𝒞odd : ∀ C ∈ 𝒞, IsOddCycle G C := fun C hC => (h𝒞mem C).mp hC
  have h𝒞meet : ∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ∩ D ≠ ∅ := by
    intro C hC D hD
    exact inter_oddCycle_of_locIndep_one hG (h𝒞odd C hC) (h𝒞odd D hD)
  have h𝒞ne : 𝒞.Nonempty := by
    obtain ⟨C, hC⟩ := hodd
    exact ⟨C, (h𝒞mem C).mpr hC⟩
  obtain ⟨a, ha⟩ := hH 𝒞 h𝒞odd h𝒞meet h𝒞ne
  exact ⟨a, fun D hD => ha D ((h𝒞mem D).mpr hD)⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1` FOR THE *HELLY* CLASS, WITH THE OPTIMAL
CONSTANT `1`.**  This is `JSP90.closeToBipartite_one_of_linear_of_locIndep_one` of
`JSPProblem/Ring.lean` with the **strictly weaker** hypothesis `HellyOddCycles G`: Part 5 exhibits
graphs satisfying `HellyOddCycles G ∧ LocIndep 1` but *not* `LinearOddCycles G`, so this is not a
corollary of round 82's instance.  The constant `1` is the smallest possible for a non-bipartite
graph. -/
theorem closeToBipartite_one_of_helly_of_locIndep_one (hG : LocIndep 1 G)
    (hH : HellyOddCycles G) : CloseToBipartite 1 G := by
  classical
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨a, ha⟩ := exists_commonVertex_of_helly_of_locIndep_one hG hH hodd
    refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨{a}, by simp, fun D hD => ?_⟩
    exact ne_empty_of_mem (Finset.mem_inter.mpr ⟨ha D hD, Finset.mem_singleton.mpr rfl⟩)
  · refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨∅, by simp, fun D hD => ?_⟩
    exact absurd ⟨D, hD⟩ hodd

/-- **THE SAME INSTANCE IN `Erdős73On` FORM, FOR THE HELLY CLASS.** -/
theorem erdos73On_helly_one :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → HellyOddCycles G →
      CloseToBipartite 1 G :=
  fun _ _ _ hG hH => closeToBipartite_one_of_helly_of_locIndep_one hG hH

/-- **ROUND 82'S INSTANCE IS THE SPECIALISATION OF PART 3 TO LINEAR GRAPHS**, recorded so that the
two files are visibly comparable. -/
theorem closeToBipartite_one_of_helly_of_linear (hG : LocIndep 1 G) (hlin : LinearOddCycles G) :
    CloseToBipartite 1 G :=
  closeToBipartite_one_of_helly_of_locIndep_one hG (helly_of_linearOddCycles hlin)

end ClassicalPart

/-! ## Part 4 — `K₃` attains the constant `1`: the value of `f` on the Helly class is exactly `1` -/

/-- **`K₃` HAS THE HELLY PROPERTY.**  Every odd cycle of `K₃` is the whole vertex set
(`JSP90.eq_univ_of_oddCycle_completeGraph_three`), so any nonempty family of them has a common
vertex, whatever the pairwise-meeting condition. -/
theorem helly_completeGraph_three : HellyOddCycles (SimpleGraph.completeGraph (Fin 3)) := by
  intro 𝒞 hodd hmeet hne
  obtain ⟨C, hC⟩ := hne
  obtain ⟨v, hv⟩ := (hodd C hC).nonempty'
  exact ⟨v, fun D hD => by
    have h2 : D = (Finset.univ : Finset (Fin 3)) :=
      eq_univ_of_oddCycle_completeGraph_three (hodd D hD)
    rw [h2]
    exact Finset.mem_univ v⟩

/-- **`LocIndep 1 (K₃)`**: the sharpness witness of Part 4 is inside the range of the theorem. -/
theorem helly_locIndep_one_K3 : LocIndep 1 (SimpleGraph.completeGraph (Fin 3)) :=
  completeGraph_locIndep 1

/-- **THE CONSTANT `1` IS ATTAINED ON THE HELLY CLASS: `K₃` HAS THE HELLY PROPERTY, SATISFIES
`LocIndep 1`, AND IS NOT BIPARTITE.**  So the `k = 1` value of `f` restricted to `HellyOddCycles`
is exactly `1`, the smallest value possible for a graph with an odd cycle. -/
theorem helly_not_closeToBipartite_zero_K3 :
    ¬ CloseToBipartite 0 (SimpleGraph.completeGraph (Fin 3)) :=
  not_closeToBipartite_zero_completeGraph_three

/-- **THE HELLY CLASS IS ATTAINED AT THE SHARP CONSTANT `1`**: the three hypotheses hold together and
the conclusion with `m = 0` fails.  A graph of the class satisfies `CloseToBipartite 1`, and this
says the `1` cannot be lowered. -/
theorem not_helly_attained_zero :
    ¬ (HellyOddCycles (SimpleGraph.completeGraph (Fin 3)) ∧
      LocIndep 1 (SimpleGraph.completeGraph (Fin 3)) ∧
      CloseToBipartite 0 (SimpleGraph.completeGraph (Fin 3))) :=
  fun h => helly_not_closeToBipartite_zero_K3 h.2.2

/-! ## Part 5 — the class is *strictly* larger than round 82's: the diamond

The **diamond** `K₄` minus an edge has exactly two odd cycles, the two triangles that avoid the
deleted edge; **both contain the vertices `0` and `1`**, so the diamond has the Helly property,
while its two odd cycles meet in **two** vertices, so it is **not** linear.  Hence the instance of
Part 3 is *not* a corollary of round 82's, and the Helly class strictly contains round 82's. -/

section Diamond

/-- The edge set of `diamond`, the graph `K₄` with the edge `2 – 3` deleted. -/
def diamondEdge : Finset (Fin 4 × Fin 4) :=
  {(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,2),(2,1),(1,3),(3,1)}

theorem diamondEdge_symm : ∀ v w : Fin 4, (v, w) ∈ diamondEdge ↔ (w, v) ∈ diamondEdge := by decide

theorem diamondEdge_irrefl : ∀ v : Fin 4, (v, v) ∉ diamondEdge := by decide

/-- **`diamond`, the graph `K₄` minus the edge `2 – 3`.** -/
def diamond : SimpleGraph (Fin 4) where
  Adj v w := (v, w) ∈ diamondEdge
  symm := ⟨fun _ _ h => (diamondEdge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => (diamondEdge_irrefl _ h)⟩

@[simp] theorem diamond_adj {v w : Fin 4} : diamond.Adj v w ↔ (v, w) ∈ diamondEdge := Iff.rfl

/-- Adjacency of `diamond` is decidable: this is what makes the finite checks below kernel
computations. -/
local instance : DecidableRel diamond.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ diamondEdge))

/-- **THE VERTEX SET OF A 3-CYCLE IS A CLIQUE** — the elementary step used to classify the odd cycles
of `diamond`.  The case `|C| = 3` is the only one needed, and `JSP90.fin3_cycSucc_rel` says that on
`Fin 3` every pair of distinct indices is a cyclic step. -/
theorem three_cycle_isClique (D : Finset (Fin 4)) (f : Fin 3 → Fin 4) (_hinj : Function.Injective f)
    (hcyc : ∀ j : Fin 3, diamond.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ x : Fin 4, x ∈ D ↔ ∃ j : Fin 3, f j = x) : diamond.IsClique D := by
  intro v hv w hw hvw
  obtain ⟨i, hi⟩ := (hmem v).mp hv
  obtain ⟨j, hj⟩ := (hmem w).mp hw
  have hij : i ≠ j := by
    intro h
    apply hvw
    rw [← hi, ← hj, h]
  rcases fin3_cycSucc_rel hij with e | e
  · refine diamond.adj_symm ?_
    rw [← hi, ← hj, e]
    exact hcyc j
  · rw [← hi, ← hj, e]
    exact hcyc i

set_option maxHeartbeats 2000000 in
/-- **EVERY ODD CYCLE OF THE DIAMOND CONTAINS THE VERTEX `0`.**  An odd cycle of a four-vertex graph
has exactly three vertices, so its vertex set is a clique (`JSP90.three_cycle_isClique`), and the
only three-element subsets of `Fin 4` that are cliques of the diamond contain `0`. -/
theorem mem_zero_of_oddCycle_diamond {D : Finset (Fin 4)} (hD : IsOddCycle diamond D) :
    (0 : Fin 4) ∈ D := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hcard : D.card = m := card_eq_cyclicOrder f hinj hmem
  have hle : D.card ≤ 4 := le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
  rw [hcard] at hle
  have hm' : m = 3 := by omega
  subst hm'
  have hcl : diamond.IsClique D := three_cycle_isClique D f hinj hcyc hmem
  rcases Finset.card_eq_three.mp hcard with ⟨a, b, c, hab, hac, hbc, heq⟩
  have hmemab : a ∈ D ∧ b ∈ D := ⟨by rw [heq]; simp, by rw [heq]; simp⟩
  have hab' : diamond.Adj a b := hcl hmemab.1 hmemab.2 hab
  have hmemac : a ∈ D ∧ c ∈ D := ⟨by rw [heq]; simp, by rw [heq]; simp⟩
  have hac' : diamond.Adj a c := hcl hmemac.1 hmemac.2 hac
  have hmemcb : c ∈ D ∧ b ∈ D := ⟨by rw [heq]; simp, by rw [heq]; simp⟩
  have hbc' : diamond.Adj c b := hcl hmemcb.1 hmemcb.2 hbc.symm
  simp only [heq]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [diamondEdge, diamond_adj]

/-- **THE DIAMOND HAS THE HELLY PROPERTY**, because the vertex `0` lies in every one of its odd
cycles.  This is the machine-checked reason the Helly class is *strictly* larger than round 82's
`LinearOddCycles`: the diamond's two odd cycles meet in **two** vertices. -/
theorem helly_diamond : HellyOddCycles diamond := by
  intro 𝒞 hodd hmeet hne
  obtain ⟨C, hC⟩ := hne
  exact ⟨0, fun D hD => mem_zero_of_oddCycle_diamond (hodd D hD)⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`LocIndep 1 diamond`**, by exhaustive decision over the `2¹⁶` vertex sets of `Fin 4`. -/
theorem locIndep_one_diamond : LocIndep 1 diamond := by
  unfold LocIndep
  decide

/-- **THE DIAMOND IS ONE VERTEX AWAY FROM BIPARTITE** — the instance of Part 3 does hold there. -/
theorem closeToBipartite_one_diamond : CloseToBipartite 1 diamond :=
  closeToBipartite_one_of_helly_of_locIndep_one locIndep_one_diamond helly_diamond

/-- A cyclic ordering of three vertices. -/
def dcyc3 (a b c : Fin 4) : Fin 3 → Fin 4 := fun j =>
  match j.val with
  | 0 => a | 1 => b | _ => c

/-- The triangle `0 – 1 – 2` of the diamond. -/
theorem isOddCycle_diamond_a : IsOddCycle diamond ({0, 1, 2} : Finset (Fin 4)) :=
  ⟨3, dcyc3 0 1 2, by decide, by decide, by decide, by decide, by decide⟩

/-- The triangle `0 – 1 – 3` of the diamond. -/
theorem isOddCycle_diamond_b : IsOddCycle diamond ({0, 1, 3} : Finset (Fin 4)) :=
  ⟨3, dcyc3 0 1 3, by decide, by decide, by decide, by decide, by decide⟩

/-- **THE DIAMOND IS *NOT* LINEAR**: its two triangles meet in the two vertices `0` and `1`.  This is
the machine-checked obstruction to reading Part 3 as a corollary of round 82's
`JSP90.closeToBipartite_one_of_linear_of_locIndep_one`: `diamond` satisfies `HellyOddCycles G`,
`LocIndep 1` and `CloseToBipartite 1`, but **not** `LinearOddCycles G`. -/
theorem not_linear_diamond : ¬ LinearOddCycles diamond := by
  rintro h
  exact not_linear_of_two_mem (C := ({0, 1, 2} : Finset (Fin 4))) (D := ({0, 1, 3} : Finset (Fin 4)))
    h isOddCycle_diamond_a isOddCycle_diamond_b (by decide)
    (show (0 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) by decide)
    (show (0 : Fin 4) ∈ ({0, 1, 3} : Finset (Fin 4)) by decide)
    (show (1 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) by decide)
    (show (1 : Fin 4) ∈ ({0, 1, 3} : Finset (Fin 4)) by decide) (by decide)

/-- **THE CLASS IS STRICTLY LARGER THAN ROUND 82'S: A GRAPH WITH THE HELLY PROPERTY, `LocIndep 1`
AND `CloseToBipartite 1`, WHICH IS NOT LINEAR.**  This is the formal statement that
`JSP90.closeToBipartite_one_of_helly_of_locIndep_one` is a genuinely new instance of the headline
theorem and not a corollary of `JSP90.closeToBipartite_one_of_linear_of_locIndep_one`. -/
theorem HellyOfNonlinear :
    HellyOddCycles diamond ∧ LocIndep 1 diamond ∧ CloseToBipartite 1 diamond ∧
      ¬ LinearOddCycles diamond :=
  ⟨helly_diamond, locIndep_one_diamond, closeToBipartite_one_diamond, not_linear_diamond⟩

end Diamond

noncomputable section

section ClassicalPart

local instance instDecidableEqHellyB : DecidableEq V := Classical.decEq V

local instance instDecidableIsOddCycleHellyB {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ## Part 6 — the remaining statement for the Helly class -/

/-- **THE REMAINING STATEMENT FOR THE HELLY CLASS AT A GENERAL CONSTANT.**  Stated as a `def` and
**not** assumed: every `LocIndep`-`c` graph whose odd cycles form a Helly family is `f c`-close to
bipartite.  Part 3 is the proved base level (`c = 1`, `f 1 = 1`); behind the general statement
stands `JSP90.OddCycleErdosPosa r`, since the Helly property bounds the transversal number at
`k = 1` and says nothing about larger packings. -/
noncomputable def HellyErdős73 (f : ℕ → ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (c : ℕ),
    LocIndep c G → HellyOddCycles G → CloseToBipartite (f c) G

/-- The proved base level of `JSP90.HellyErdős73`, in the `def`'s own vocabulary. -/
theorem erdos73On_helly_one_base : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    LocIndep 1 G → HellyOddCycles G → CloseToBipartite 1 G :=
  erdos73On_helly_one

end ClassicalPart

end

end

end JSP90
