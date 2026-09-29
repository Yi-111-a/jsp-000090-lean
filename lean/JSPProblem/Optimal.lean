/-
# JSP-000090, round 46 — Erdős–Pósa with the **optimal** function on graphs with pairwise
# vertex-disjoint odd cycles

## What this file is

The development so far proves the *packing* half of Erdős #73 in full
(`JSPProblem/Packing.lean`, `JSPProblem/Residue.lean`) and the *transversal* half under extra
structural hypotheses (bounded odd girth — round 40; no branch vertices — round 38; a 2-cut
decomposition — rounds 42–43; bounded packing weight — round 44).  The single missing statement is
the Erdős–Pósa theorem for odd cycles (`JSPProblem.Transversal.OddCycleErdosPosa`), i.e. the
indefinite case of "a bounded packing number yields a bounded transversal number".

This file attacks the problem from the *sharpness* side, which no previous round did.  For the
class of graphs in which **any two distinct odd cycles are vertex-disjoint**, the Erdős–Pósa
function is known and *optimal*: the packing number and the odd cycle transversal number
**coincide**.  This gives the first instance of the headline theorem whose constant `f(k) = k` is
proved, is optimal, and whose hypothesis is an intrinsic property of the *odd cycles* of `G`
(rounds 38 and 44 give optimal constants for classes defined by degrees, and for a bound on the
whole packing).

Concretely this file proves

* `erdos73On_of_disjoint_oddCycles` — **a new instance of the headline theorem**: under
  `LocIndep k`, if no two distinct odd cycles of `G` share a vertex, then `G` is the union of a
  bipartite graph and **at most `k` vertices**;
* `erdos73On_disjoint_oddCycles_iff` — **the class is exactly as hard as the general theorem as
  far as the constant is concerned**: on this class the least Erdős constant is `k` and nothing
  less works (witness `kTriangles k` of `JSPProblem/Sharp.lean`);
* `closeToBipartite_iff_packingLe` — the exact equivalence "transversal ≤ m" vs. "packing ≤ m" on
  the class, i.e. Erdős–Pósa with the *identity* function, proved and not merely quoted;
* `closeToBipartite_of_anticover` — **the composition lemma**: the conclusion of Erdős #73 is
  *additive over an anticomplete decomposition* of the vertex set (`Anticover`: the two sides are
  disjoint, cover `V`, and no edge joins them), so that the instances compose.  This is the
  composition that was missing: rounds 42–43 compose along 2-cuts, where the two sides share the
  two cut vertices and the constant is charged an extra `2`;
* `class_hypothesis_is_necessary` and `packingNumber_one_not_enough` — **machine-checked negative
  results**: `LocIndep 3 (K_5)` holds, every packing of odd cycles of `K_5` has at most one member,
  and `K_5` is nevertheless not `2`-close to bipartite.  The only reason is that two of its odd
  cycles share two vertices.  So the identity Erdős–Pósa function does *not* extend beyond the
  class, and the packing bound alone does not give the conclusion — the obstruction is inside the
  range of the headline theorem.

## Relation to the blocker

`jsp_000090_main` is still not proved; the missing statement remains the Erdős–Pósa theorem for
odd cycles.  What this file adds to that reduction is (i) the exact statement of the identity case
of the Erdős–Pósa function, machine-checked together with its optimality on a whole class of
graphs, and (ii) the negative result that the identity case does not extend to graphs in which two
odd cycles share two vertices, which is the same `K_5` obstruction already recorded for absorption
in `JSPProblem/Weight.lean`.
-/
import JSPProblem.Weight
import JSPProblem.Separator
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The instance of `DecidableEq` used throughout this file; the same one the statements of
`JSPProblem/Residue.lean` and `JSPProblem/Weight.lean` were elaborated with. -/
local instance instDecidableEqOptimal : DecidableEq V := Classical.decEq V

/-! ### Part 1 — a transversal of size `|C|` for a family of pairwise disjoint odd cycles -/

section OnePerCycle

/-- **A transversal of size `|C|` for a family `C` of pairwise disjoint nonempty finsets, provided
every odd cycle of `G` is one of the members of `C`.**

The vertex chosen for each member is `Classical.choose` of its nonemptiness; that the resulting set
is a transversal is the maximality argument of
`JSPProblem.Transversal.hitsOddCycles_of_maxCardFamily`, and that it is *injective* — hence has
size `|C|` — is the disjointness of the members. -/
theorem exists_transversal_onePerMember {C : Finset (Finset V)}
    (hC : DisjointFamily C) (hne : ∀ i ∈ C, (i : Finset V).Nonempty)
    (hall : ∀ D, IsOddCycle G D → ∃ i ∈ C, D = i) :
    ∃ X : Finset V, HitsOddCycles G X ∧ X.card = C.card := by
  classical
  set f : {i // i ∈ C} → V :=
    fun i => @Classical.choose V (fun x => x ∈ (i : Finset V)) (hne i.1 i.2) with hfdef
  have hmem : ∀ i : {i // i ∈ C}, f i ∈ (i : Finset V) := by
    intro i
    exact Classical.choose_spec _
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hEq : (i.1 : Finset V) = j.1
    · exact Subtype.ext hEq
    · have hdisj : Disjoint (i.1 : Finset V) j.1 :=
        Finset.disjoint_iff_inter_eq_empty.mpr (hC i.1 i.2 j.1 j.2 hEq)
      have hmemj : f i ∈ (j.1 : Finset V) := by
        rw [hij]
        exact hmem j
      exact absurd hmemj (Finset.disjoint_left.mp hdisj (hmem i))
  set X : Finset V := C.attach.image f with hXdef
  refine ⟨X, fun D hD => ?_, ?_⟩
  · obtain ⟨i, hi, hEq⟩ := hall D hD
    have hmemX : f ⟨i, hi⟩ ∈ X := by
      rw [hXdef]
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach C ⟨i, hi⟩, rfl⟩
    have hmemD : f ⟨i, hi⟩ ∈ D := by
      rw [hEq]
      exact hmem ⟨i, hi⟩
    have hne : (D ∩ X).Nonempty :=
      ⟨f ⟨i, hi⟩, Finset.mem_inter.mpr ⟨hmemD, hmemX⟩⟩
    exact Finset.nonempty_iff_ne_empty.mp hne
  · rw [hXdef, Finset.card_image_of_injective _ hinj, Finset.card_attach]

/-- **A transversal of a packing of pairwise disjoint finsets is at least as large as the
packing**: `|X| ≥ |C|` whenever `X` meets every member of the disjoint family `C`.  This is the
counting half of the identity Erdős–Pósa function. -/
theorem card_le_of_hitsOddCycles_of_disjointFamily {C : Finset (Finset V)} {X : Finset V}
    (hC : DisjointFamily C) (_hne : ∀ i ∈ C, (i : Finset V).Nonempty)
    (hX : ∀ i ∈ C, i ∩ X ≠ ∅) : C.card ≤ X.card := by
  classical
  have hsub : X ∩ C.biUnion id ⊆ X := Finset.inter_subset_left
  have hinter : ∀ i ∈ C, (X ∩ C.biUnion id) ∩ i = X ∩ i := by
    intro i hi
    ext x
    constructor
    · intro hx
      obtain ⟨hxXU, hxi⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxX, -⟩ := Finset.mem_inter.mp hxXU
      exact Finset.mem_inter.mpr ⟨hxX, hxi⟩
    · intro hx
      obtain ⟨hxX, hxi⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨hxX, Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩⟩, hxi⟩
  have hcov : ∀ ⦃x : V⦄, x ∈ X ∩ C.biUnion id → ∃ i ∈ C, x ∈ i := by
    intro x hx
    exact Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
  have hcard : (X ∩ C.biUnion id).card = ∑ i ∈ C, (X ∩ i).card := by
    rw [card_eq_sum_card_inter_of_disjoint hC hcov,
      Finset.sum_congr rfl (fun i hi => by rw [hinter i hi])]
  have hle : (∑ i ∈ C, (1 : ℕ)) ≤ ∑ i ∈ C, (X ∩ i).card := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hhit : X ∩ i ≠ ∅ := by rw [Finset.inter_comm]; exact hX i hi
    exact Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hhit)
  have hones : (∑ i ∈ C, (1 : ℕ)) = C.card := (Finset.card_eq_sum_ones C).symm
  have hleX : (X ∩ C.biUnion id).card ≤ X.card := Finset.card_le_card hsub
  omega

end OnePerCycle

/-! ### Part 2 — the class in which the packing number and the transversal number agree -/

section DisjointOddCycles

/-- **The odd cycles of `G` are pairwise vertex-disjoint**: any two odd cycles of `G` are equal or
disjoint.  This is the hypothesis of the identity case of Erdős–Pósa proved below; it says nothing
about the degrees, the lengths, or the number of the odd cycles. -/
def OddCyclesDisjoint (G : SimpleGraph V) : Prop :=
  ∀ C D : Finset V, IsOddCycle G C → IsOddCycle G D → C = D ∨ C ∩ D = ∅

/-- A packing of odd cycles is a family of pairwise disjoint finsets in this class. -/
theorem IsOddCycleFamily.disjointFamily_of_oddCyclesDisjoint (h : OddCyclesDisjoint G)
    {C : Finset (Finset V)} (hC : IsOddCycleFamily (G := G) C) : DisjointFamily C := by
  intro X hX Y hY hXY
  rcases h X Y (hC.2 X hX) (hC.2 Y hY) with h' | h'
  · exact absurd h' hXY
  · exact h'

/-- **Every odd cycle of `G` is a member of a maximum packing, in this class.**  A maximum packing
meets every odd cycle (`JSPProblem.Transversal.hitsOddCycles_of_maxCardFamily`), and in this class
a member of the packing it meets is equal to it. -/
theorem mem_of_oddCycle_of_maxPacking {C : Finset (Finset V)} (h : OddCyclesDisjoint G)
    (hC : IsOddCycleFamily (G := G) C) (hmax : ∀ D, IsOddCycleFamily (G := G) D → D.card ≤ C.card)
    {D : Finset V} (hD : IsOddCycle G D) : D ∈ C := by
  classical
  have hcov : ∀ ⦃x : V⦄, x ∈ C.biUnion id → ∃ i ∈ C, x ∈ i := by
    intro x hx
    exact Finset.mem_biUnion.mp hx
  have hhit : D ∩ C.biUnion id ≠ ∅ := hitsOddCycles_of_maxCardFamily hC hmax D hD
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hhit
  obtain ⟨i, hi, hxi⟩ := hcov ((Finset.mem_inter.mp hx).2)
  rcases h D i hD (hC.2 i hi) with hDi | hDi
  · exact hDi ▸ hi
  · have hxD : x ∈ D := (Finset.mem_inter.mp hx).1
    have hxni : x ∉ i :=
      Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr hDi) hxD
    exact absurd hxi hxni

/-- **A maximum packing yields a transversal of the same size.**  In the class `OddCyclesDisjoint`
the odd cycle transversal number equals the odd cycle packing number, and this is the realization
step: one vertex per member of a maximum packing (`exists_transversal_onePerMember`, which uses
`mem_of_oddCycle_of_maxPacking`). -/
theorem exists_maxPacking_and_transversal (h : OddCyclesDisjoint G) :
    ∃ C : Finset (Finset V), ∃ X : Finset V, IsOddCycleFamily (G := G) C ∧ HitsOddCycles G X ∧
      X.card = C.card ∧ ∀ D : Finset (Finset V), IsOddCycleFamily (G := G) D → D.card ≤ C.card := by
  classical
  obtain ⟨C, hC, hmax⟩ := exists_maxCard_oddCycleFamily (G := G)
  have hne : ∀ i ∈ C, (i : Finset V).Nonempty := fun i hi => (hC.2 i hi).nonempty
  have hall : ∀ D, IsOddCycle G D → ∃ i ∈ C, D = i :=
    fun D hD => ⟨D, mem_of_oddCycle_of_maxPacking h hC hmax hD, rfl⟩
  obtain ⟨X, hX, hcard⟩ :=
    exists_transversal_onePerMember (C := C) (hC.disjointFamily_of_oddCyclesDisjoint h) hne hall
  exact ⟨C, X, hC, hX, hcard, hmax⟩

/-- **Erdős–Pósa for odd cycles with the IDENTITY function, in the class of pairwise disjoint odd
cycles**: `G` is the union of a bipartite graph and at most `m` vertices **iff** every packing of
odd cycles of `G` has at most `m` members.

This is the whole content of the class in one statement: the two numbers — the least size of an odd
cycle transversal and the largest size of an odd cycle packing — are equal. -/
theorem closeToBipartite_iff_packingLe (h : OddCyclesDisjoint G) (m : ℕ) :
    CloseToBipartite m G ↔ ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ m := by
  classical
  constructor
  · rintro ⟨X, hX, hb⟩
    intro C hC
    have hle := card_le_of_hitsOddCycles_of_disjointFamily (C := C)
      (hC.disjointFamily_of_oddCyclesDisjoint h)
      (fun i hi => (hC.2 i hi).nonempty)
      (fun i hi => hitsOddCycles_of_isBipartite_delete hb i (hC.2 i hi))
    exact hle.trans hX
  · intro hle
    obtain ⟨C, X, hC, hHits, hcard, hmax⟩ := exists_maxPacking_and_transversal h
    refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr
      ⟨X, Nat.le_trans (Nat.le_of_eq hcard) (hle C hC), hHits⟩

/-- **Monotonicity of `CloseToBipartite` in the number of deleted vertices.** -/
theorem closeToBipartite.mono {a b : ℕ} (h : a ≤ b) (hc : CloseToBipartite a G) :
    CloseToBipartite b G := by
  obtain ⟨X, hX, hb⟩ := hc
  exact ⟨X, hX.trans h, hb⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, with the optimal constant `f(k) = k`.**

Let `G` satisfy Erdős's local hypothesis `LocIndep k`, and suppose no two distinct odd cycles of
`G` share a vertex.  Then `G` is the union of a bipartite graph and at most `k` vertices.

No bound on the odd girth is used, no bound on the number of branch vertices is used, and there is
no extra parameter: the constant is the parameter `k` itself.  The proof is
`closeToBipartite_iff_packingLe` in the `←` direction together with
`JSPProblem.Transversal.LocIndep.oddCycleFamily_card_le`: the whole content is that a transversal
is as large as a packing in this class. -/
theorem erdos73On_of_disjoint_oddCycles (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → OddCyclesDisjoint G → CloseToBipartite k G := by
  intro W instW G hG h
  exact (closeToBipartite_iff_packingLe h k).mpr fun C hC => hG.oddCycleFamily_card_le hC

end DisjointOddCycles

/-! ### Part 3 — the odd cycles of `kTriangles k` are pairwise disjoint, and the class is sharp -/

section SharpClass

variable {k : ℕ}

local instance : DecidableEq (Fin 3 × Fin k) := Classical.decEq _
local instance : DecidableEq (Finset (Fin 3 × Fin k)) := Classical.decEq _
local instance : DecidableEq (Finset (Finset (Fin 3 × Fin k))) := Classical.decEq _

/-- **The odd cycles of `kTriangles k` are exactly the `k` fibres.**  Consecutive vertices of a
cycle are adjacent, hence lie in the same fibre; the cyclic successor reaches every position of
the numbering (`CycleOrder.exists_iter` of `JSPProblem/Branch.lean`), so the whole cycle lies in
one fibre, which has three vertices; and a cycle has at least three of them, so it is the whole
fibre. -/
theorem oddCycle_eq_tri_of_kTriangles {C : Finset (Fin 3 × Fin k)}
    (hC : IsOddCycle (kTriangles k) C) : ∃ i : Fin k, C = tri i := by
  classical
  obtain ⟨o, -⟩ := hC.cycleOrder
  have ho3 : 0 < o.m := lt_of_lt_of_le (by decide) o.hm3
  set o0 : Fin o.m := ⟨0, ho3⟩ with ho0
  have hstep : ∀ j : Fin o.m, (o.f (cycSucc j)).2 = (o.f j).2 := by
    intro j
    exact (kTriangles_adj.mp (o.hcyc j)).1.symm
  have hkey : ∀ t : ℕ, ((o.f ((cycSucc^[t] : Fin o.m → Fin o.m) o0)).2) = (o.f o0).2 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact (hstep _).trans ih
  have hall : ∀ j : Fin o.m, (o.f j).2 = (o.f o0).2 := by
    intro j
    obtain ⟨t, -, ht⟩ := CycleOrder.exists_iter o o0 j
    rw [← ht]
    exact hkey t
  have hCe : C = (Finset.univ : Finset (Fin o.m)).image o.f := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (o.hmem x).mp hx
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    · intro hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact (o.hmem x).mpr ⟨j, hj⟩
  have hcardC : C.card = o.m := by
    have h1 := congrArg Finset.card hCe
    have h2 := Finset.card_image_of_injective (Finset.univ : Finset (Fin o.m)) o.hinj
    have h3 : ((Finset.univ : Finset (Fin o.m)).image o.f).card = o.m := by rw [h2]; simp
    exact h1.trans h3
  have hsub : C ⊆ tri (o.f o0).2 := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hCe ▸ hx)
    exact (mem_tri).mpr (by rw [← hj]; exact hall j)
  refine ⟨(o.f o0).2, Finset.Subset.antisymm hsub ?_⟩
  by_contra hn
  have hne : C ≠ tri (o.f o0).2 := by
    intro he
    exact hn (he ▸ Finset.Subset.rfl)
  have hss : C ⊂ tri (o.f o0).2 := (Finset.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩
  exact absurd (Finset.card_lt_card hss) (by
    rw [hcardC, card_tri]
    intro hlt
    exact (Nat.not_le_of_gt hlt) o.hm3)

/-- **The witness of `JSPProblem/Sharp.lean` lies in the class of `Part 2`.** -/
theorem oddCyclesDisjoint_kTriangles : OddCyclesDisjoint (kTriangles k) := by
  intro C D hC hD
  obtain ⟨i, rfl⟩ := oddCycle_eq_tri_of_kTriangles hC
  obtain ⟨j, rfl⟩ := oddCycle_eq_tri_of_kTriangles hD
  by_cases h : i = j
  · exact Or.inl (h ▸ rfl)
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mp (tri_disjoint h))

/-- **THE CLASS IS EXACTLY AS HARD AS THE GENERAL THEOREM AS FAR AS THE CONSTANT IS CONCERNED.**

For the class of graphs of `OddCyclesDisjoint`, the least `m` for which the conclusion of Erdős #73
holds *for every* `G` of the class satisfying `LocIndep k` is exactly `k`:

* for `k ≤ m`, `erdos73On_of_disjoint_oddCycles` gives `CloseToBipartite k G` and
  `closeToBipartite.mono` upgrades it to `m`;
* for `m < k`, the witness `kTriangles k` of `JSPProblem/Sharp.lean` satisfies `LocIndep k` and
  lies in the class, while `closeToBipartite_iff` says it is not `m`-close to bipartite.

So `erdos73On_of_disjoint_oddCycles` is *optimal*: the constant `k` cannot be lowered on this
class, and the class is a genuine subcase of Erdős #73 with a *decided* answer — in contrast with
the general statement, whose best constant is the open Erdős–Pósa function. -/
theorem erdos73On_disjoint_oddCycles_iff (k m : ℕ) :
    (∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
        LocIndep k G → OddCyclesDisjoint G → CloseToBipartite m G) ↔ k ≤ m := by
  constructor
  · intro h
    have h' := h (Fin 3 × Fin k) inferInstance (kTriangles k) locIndep_kTriangles
      oddCyclesDisjoint_kTriangles
    exact (closeToBipartite_iff (k := k) (m := m)).mp h'
  · intro hX
    intro W instW G hG h
    exact (erdos73On_of_disjoint_oddCycles k W instW G hG h).mono hX

end SharpClass

/-! ### Part 4 — the class hypothesis is necessary: `K_5` -/

section KFive

local instance instDecidableEqFinNOptimal (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-- **Any two odd cycles of a complete graph on at most `5` vertices meet**: each has at least
`3` vertices, and the counting `|C| + |D| = |C ∩ D| + |C ∪ D|` with `|C ∪ D| ≤ n ≤ 5` forces
`|C ∩ D| ≥ 6 - n ≥ 1`. -/
theorem inter_nonempty_of_oddCycles_card {n : ℕ} {C D : Finset (Fin n)}
    (hC : IsOddCycle (SimpleGraph.completeGraph (Fin n)) C)
    (hD : IsOddCycle (SimpleGraph.completeGraph (Fin n)) D) (hn : n ≤ 5) : C ∩ D ≠ ∅ := by
  have h3C := isOddCycle_card_ge_three hC
  have h3D := isOddCycle_card_ge_three hD
  have hsubU : C ∪ D ⊆ (Finset.univ : Finset (Fin n)) := by
    intro x _
    exact Finset.mem_univ x
  have hcardU : (C ∪ D).card ≤ n := (Finset.card_le_card hsubU).trans (by simp)
  have h1 : 6 ≤ C.card + D.card := by omega
  have h2 : C.card + D.card = (C ∪ D).card + (C ∩ D).card :=
    (Finset.card_union_add_card_inter C D).symm
  have h4 : 0 < (C ∩ D).card := by omega
  exact Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h4)

/-- **No two odd cycles of `K_5` are disjoint.** -/
theorem inter_ne_empty_of_oddCycles_completeGraph_five {C D : Finset (Fin 5)}
    (hC : IsOddCycle (SimpleGraph.completeGraph (Fin 5)) C)
    (hD : IsOddCycle (SimpleGraph.completeGraph (Fin 5)) D) : C ∩ D ≠ ∅ :=
  inter_nonempty_of_oddCycles_card hC hD (by omega)

/-- **Every packing of odd cycles of `K_5` has at most one member**: the odd cycles of `K_5` all
meet, so a packing — a family of pairwise *disjoint* odd cycles — has cardinality at most one. -/
theorem packing_card_le_one_completeGraph_five {C : Finset (Finset (Fin 5))}
    (hC : IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin 5)) C) : C.card ≤ 1 := by
  by_contra hn
  have h2 : 2 ≤ C.card := by omega
  obtain ⟨X, hX, Y, hY, hXY⟩ := exists_two_of_card_ge_two h2
  have hdis : X ∩ Y = ∅ := hC.1 X hX Y hY hXY
  exact absurd hdis (inter_ne_empty_of_oddCycles_completeGraph_five (hC.2 X hX) (hC.2 Y hY))

/-- **The `5`-cycle `0 - 1 - 2 - 3 - 4 - 0` of `K_5`, as a finset of vertices.** -/
def fiveCycle : Finset (Fin 5) :=
  (Finset.univ : Finset (Fin 5)).image fun j : Fin 5 => (⟨j.val, by omega⟩ : Fin 5)

theorem mem_fiveCycle (i : Fin 5) : i ∈ fiveCycle := by
  rw [fiveCycle]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- **A step of the cyclic successor is not the identity** (counting: `j + 1 % n ≠ j` for
`j < n`, `1 < n`).  This is the general form of `JSPProblem.Sharp.cycSucc_three_ne`. -/
theorem cycSucc_ne_self {m : ℕ} (hm : 1 < m) (j : Fin m) : j ≠ cycSucc j := by
  have h3 := cycSucc_pow_inj j (p := 1) (q := 0) (by omega) (by omega) (by decide)
  rw [Function.iterate_one, Function.iterate_zero] at h3
  exact fun h => h3 h.symm

set_option maxHeartbeats 800000 in
/-- **The `5`-cycle `0 - 1 - 2 - 3 - 4 - 0` is an odd cycle of `K_5`**: a Hamiltonian odd cycle of
the complete graph, whose vertex set is everything. -/
theorem isOddCycle_fiveCycle : IsOddCycle (SimpleGraph.completeGraph (Fin 5)) fiveCycle := by
  rw [fiveCycle]
  refine isOddCycle_image (fun j : Fin 5 => (⟨j.val, by omega⟩ : Fin 5)) (by rfl) (by decide) ?_ ?_
  · intro i j h
    exact Fin.ext (congrArg Fin.val h)
  · intro j
    exact fun hcon => cycSucc_ne_self (m := 5) (by omega) j (Fin.ext (congrArg Fin.val hcon))

/-- **`K_5` is not in the class of `Part 2`**: the triangle `{0, 1, 2}` and the `5`-cycle
`0 - 1 - 2 - 3 - 4 - 0` share the two vertices `0` and `1`. -/
theorem not_oddCyclesDisjoint_completeGraph_five :
    ¬ OddCyclesDisjoint (SimpleGraph.completeGraph (Fin 5)) := by
  intro h
  rcases h ({(0 : Fin 5), 1, 2} : Finset (Fin 5)) fiveCycle
    isOddCycle_completeGraph_five_triangle isOddCycle_fiveCycle with hEq | hdis
  · have hne : ({(0 : Fin 5), 1, 2} : Finset (Fin 5)) ≠ fiveCycle := by
      intro he
      have h4 : (4 : Fin 5) ∈ ({(0 : Fin 5), 1, 2} : Finset (Fin 5)) := he ▸ mem_fiveCycle 4
      have hnot : (4 : Fin 5) ∉ ({(0 : Fin 5), 1, 2} : Finset (Fin 5)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff]
        omega
      exact absurd h4 hnot
    exact absurd hEq hne
  · have hmem0 : (0 : Fin 5) ∈ ({(0 : Fin 5), 1, 2} : Finset (Fin 5)) := Finset.mem_insert_self _ _
    have hne : ({(0 : Fin 5), 1, 2} : Finset (Fin 5)) ∩ fiveCycle ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp
        ⟨0, Finset.mem_inter.mpr ⟨hmem0, mem_fiveCycle 0⟩⟩
    exact absurd hdis hne

/-- **THE CLASS HYPOTHESIS OF `erdos73On_of_disjoint_oddCycles` IS NECESSARY.**

`K_5` satisfies the local hypothesis of the headline theorem with `k = 3`
(`locIndep_completeGraph_five_three`), all of its odd cycle packings have at most one member
(`packing_card_le_one_completeGraph_five`), and nevertheless it needs `3` deletions to become
bipartite — by `closeToBipartite_iff_completeGraph_add_two` of `JSPProblem/Weight.lean` it is not
`2`-close to bipartite.  The single reason is `not_oddCyclesDisjoint_completeGraph_five`: two of
its odd cycles share two vertices.  The identity Erdős–Pósa function therefore does **not** extend
beyond the class of `Part 2`, and the obstruction is visible in an explicit five-vertex graph
inside the range of the headline theorem. -/
theorem class_hypothesis_is_necessary :
    LocIndep 3 (SimpleGraph.completeGraph (Fin 5)) ∧
    ¬ OddCyclesDisjoint (SimpleGraph.completeGraph (Fin 5)) ∧
    (∀ C : Finset (Finset (Fin 5)),
        IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin 5)) C → C.card ≤ 1) ∧
    ¬ CloseToBipartite 2 (SimpleGraph.completeGraph (Fin 5)) ∧
    CloseToBipartite 3 (SimpleGraph.completeGraph (Fin 5)) :=
  ⟨locIndep_completeGraph_five_three, not_oddCyclesDisjoint_completeGraph_five,
    fun C hC => packing_card_le_one_completeGraph_five hC,
    fun h => by
      have h' := (closeToBipartite_iff_completeGraph_add_two (m := 2) (n := 5)).mp h
      omega,
    (closeToBipartite_iff_completeGraph_add_two (m := 3) (n := 5)).mpr (by omega)⟩

/-- **A packing number of one does not give a transversal of size two.**  This is the
machine-checked content of the open direction of Erdős–Pósa for odd cycles at `r = 1`, visible on
the smallest witness: the packing bound holds (all packings of `K_5` have at most one member) and
the conclusion with `m = 2` fails.  Together with `erdos73On_of_disjoint_oddCycles` it shows that
the identity function of `closeToBipartite_iff_packingLe` needs the intersection hypothesis and
cannot be deduced from the packing bound alone. -/
theorem packingNumber_one_not_enough :
    ¬ (∀ (C : Finset (Finset (Fin 5))),
        IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin 5)) C → C.card ≤ 1 →
        CloseToBipartite 2 (SimpleGraph.completeGraph (Fin 5))) := by
  intro h
  set T : Finset (Fin 5) := {(0 : Fin 5), 1, 2} with hTdef
  have hfam : IsOddCycleFamily (G := SimpleGraph.completeGraph (Fin 5)) ({T} : Finset (Finset (Fin 5))) := by
    refine ⟨fun X hX Y hY hXY => ?_, fun X hX => ?_⟩
    · have hXC : X = T := Finset.mem_singleton.mp hX
      have hYC : Y = T := Finset.mem_singleton.mp hY
      exact False.elim (absurd (hXC.trans hYC.symm) hXY)
    · exact (Finset.mem_singleton.mp hX) ▸ (hTdef ▸ isOddCycle_completeGraph_five_triangle)
  have hbad := h _ hfam (by simp)
  have h' := (closeToBipartite_iff_completeGraph_add_two (m := 2) (n := 5)).mp hbad
  omega


/-! ### Part 5 — the conclusion is additive over an anticomplete decomposition -/

section Anticover

/-- **`A` and `B` split the vertices of `G` anticompletely**: they are disjoint, they cover `V`,
and no edge of `G` joins `A` to `B`.  The two induced subgraphs `G[A]` and `G[B]` then share no
vertex and no edge, and their union is `G`. -/
def Anticover (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ ⦃x : V⦄, x ∈ A → x ∉ B) ∧ A ∪ B = (Finset.univ : Finset V) ∧
    ∀ v ∈ A, ∀ w ∈ B, ¬ G.Adj v w

/-- The two sides of an `Anticover` do not intersect. -/
theorem Anticover.disjoint (h : Anticover G A B) : ∀ ⦃x : V⦄, x ∈ A → x ∉ B := h.1

/-- ... and symmetrically. -/
theorem Anticover.disjoint' (h : Anticover G A B) : ∀ ⦃x : V⦄, x ∈ B → x ∉ A :=
  fun _ hxB hxA => h.1 hxA hxB

theorem Anticover.cover (h : Anticover G A B) : A ∪ B = (Finset.univ : Finset V) := h.2.1

theorem Anticover.anticomplete (h : Anticover G A B) {v : V} (hv : v ∈ A) {w : V} (hw : w ∈ B) :
    ¬ G.Adj v w := h.2.2 v hv w hw

/-- **Bipartiteness is additive over an anticomplete decomposition.**  If the vertices of a set
`s` are covered by the two sides of an `Anticover`, and the induced subgraphs on `s ∩ A` and on
`s ∩ B` are bipartite, then so is `G[s]`: the two 2-colourings are pasted together, because no
edge joins the two sides. -/
theorem isBipartite_induceFinset_of_anticover [Fintype V] {A B s : Finset V}
    (h : Anticover G A B) (hs : s ⊆ A ∪ B)
    (hsA : (induceFinset G (s ∩ A)).IsBipartite) (hsB : (induceFinset G (s ∩ B)).IsBipartite) :
    (induceFinset G s).IsBipartite := by
  obtain ⟨fA, hfA⟩ := hsA
  obtain ⟨fB, hfB⟩ := hsB
  refine ⟨fun v => if hvA : v ∈ A then fA v else fB v, fun {v w} hv => ?_⟩
  have hvs : v ∈ s ∧ w ∈ s ∧ G.Adj v w := by
    rw [induce_adj] at hv
    exact hv
  by_cases h1 : v ∈ A
  · by_cases h1w : w ∈ A
    · have hvw := hfA (by
        rw [induce_adj]
        exact ⟨Finset.mem_inter.mpr ⟨hvs.1, h1⟩, Finset.mem_inter.mpr ⟨hvs.2.1, h1w⟩, hvs.2.2⟩)
      simpa [h1, h1w, SimpleGraph.top_adj] using hvw
    · have hwB : w ∈ B := (Finset.mem_union.mp (hs hvs.2.1)).resolve_left h1w
      exact absurd hvs.2.2 (h.anticomplete h1 hwB)
  · have h2 : v ∈ B := (Finset.mem_union.mp (hs hvs.1)).resolve_left h1
    by_cases h2w : w ∈ B
    · have hwA : w ∉ A := h.disjoint' h2w
      have hvw := hfB (by
        rw [induce_adj]
        exact ⟨Finset.mem_inter.mpr ⟨hvs.1, h2⟩, Finset.mem_inter.mpr ⟨hvs.2.1, h2w⟩, hvs.2.2⟩)
      simpa [h1, hwA, h2w, SimpleGraph.top_adj] using hvw
    · have hwA : w ∈ A := (Finset.mem_union.mp (hs hvs.2.1)).resolve_right h2w
      exact absurd hvs.2.2.symm (h.anticomplete hwA h2)

/-- **Bipartiteness of `G` from bipartiteness on the two sides of an `Anticover`.** -/
theorem isBipartite_of_anticover (h : Anticover G A B)
    (hA : (induceFinset G A).IsBipartite) (hB : (induceFinset G B).IsBipartite) :
    G.IsBipartite := by
  have hid : induceFinset G (Finset.univ : Finset V) = G := by
    ext v w
    simp [induce_adj]
  rw [← hid]
  refine isBipartite_induceFinset_of_anticover (s := (Finset.univ : Finset V)) h
    (by rw [← h.cover]) ?_ ?_
  · simpa using hA
  · simpa using hB

/-- `deleteFinset (induceFinset G A) X` is the induced subgraph on `A \ X`. -/
theorem deleteFinset_induceFinset (A X : Finset V) :
    deleteFinset (induceFinset G A) X = induceFinset G (A \ X) := by
  ext v w
  simp only [deleteFinset_adj, induce_adj, Finset.mem_sdiff, and_assoc, and_left_comm]

/-- `A \ (X ∩ A) = A \ X`. -/
theorem sdiff_inter_self (A X : Finset V) : A \ (X ∩ A) = A \ X := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, and_comm]
  tauto

/-- `A \ (X₁ ∪ X₂) = A \ X₁` when `X₂` misses `A`. -/
theorem sdiff_union_left (A X₁ X₂ : Finset V) (h : ∀ x, x ∈ X₂ → x ∉ A) :
    A \ (X₁ ∪ X₂) = A \ X₁ := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, and_comm]
  tauto

/-- Two sets covering `V` anticompletely and missing `X` split the complement of `X`. -/
theorem sdiff_univ_eq (A B X : Finset V) (hAB : A ∪ B = (Finset.univ : Finset V))
    (_hdisj : ∀ x, x ∈ A → x ∉ B) : (A \ X) ∪ (B \ X) = (Finset.univ : Finset V) \ X := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro hx
    rcases hx with h1 | h1
    · exact ⟨hAB ▸ Finset.mem_union.mpr (Or.inl h1.1), h1.2⟩
    · exact ⟨hAB ▸ Finset.mem_union.mpr (Or.inr h1.1), h1.2⟩
  · intro hx
    rcases hx with ⟨hxu, hxX⟩
    rcases Finset.mem_union.mp (hAB.symm ▸ hxu) with h1 | h1
    · exact Or.inl ⟨h1, hxX⟩
    · exact Or.inr ⟨h1, hxX⟩

/-- **THE COMPOSITION LEMMA: the conclusion of Erdős #73 is additive over an anticomplete
decomposition.**  If the vertices of `G` split anticompletely into `A` and `B`, `G[A]` is
`m₁`-close to bipartite and `G[B]` is `m₂`-close to bipartite, then `G` is `m₁ + m₂`-close to
bipartite.

This is the composition that was missing: rounds 42–43 compose the conclusion along 2-cuts, where
the two sides are *not* anticomplete (the two cut vertices are shared) and the constant is charged
an extra `2`; here the two sides share nothing at all and the constants simply add. -/
theorem closeToBipartite_of_anticover {m₁ m₂ : ℕ} (h : Anticover G A B)
    (h₁ : CloseToBipartite m₁ (induceFinset G A)) (h₂ : CloseToBipartite m₂ (induceFinset G B)) :
    CloseToBipartite (m₁ + m₂) G := by
  obtain ⟨X₁, hX₁, hb₁⟩ := h₁
  obtain ⟨X₂, hX₂, hb₂⟩ := h₂
  have hcard₁ : (X₁ ∩ A).card ≤ m₁ :=
    le_trans (Finset.card_le_card (Finset.inter_subset_left : X₁ ∩ A ⊆ X₁)) hX₁
  have hcard₂ : (X₂ ∩ B).card ≤ m₂ :=
    le_trans (Finset.card_le_card (Finset.inter_subset_left : X₂ ∩ B ⊆ X₂)) hX₂
  have hgA : (induceFinset G (A \ (X₁ ∩ A))).IsBipartite := by
    rw [sdiff_inter_self A X₁, ← deleteFinset_induceFinset (A := A) (X := X₁)]
    exact hb₁
  have hgB : (induceFinset G (B \ (X₂ ∩ B))).IsBipartite := by
    rw [sdiff_inter_self B X₂, ← deleteFinset_induceFinset (A := B) (X := X₂)]
    exact hb₂
  set X : Finset V := (X₁ ∩ A) ∪ (X₂ ∩ B) with hXdef
  have hcardX : X.card ≤ m₁ + m₂ := by
    rw [hXdef]
    calc (X₁ ∩ A ∪ X₂ ∩ B).card ≤ (X₁ ∩ A).card + (X₂ ∩ B).card := Finset.card_union_le _ _
      _ ≤ m₁ + m₂ := Nat.add_le_add hcard₁ hcard₂
  have hkey : deleteFinset G X = induceFinset G ((A \ X) ∪ (B \ X)) := by
    rw [deleteFinset_eq_induceFinset X, sdiff_univ_eq A B X h.cover h.disjoint]
  have hd : ∀ x, x ∈ A → x ∉ B := fun _ hx1 hx2 => h.disjoint hx1 hx2
  have hd' : ∀ x, x ∈ B → x ∉ A := fun _ hx1 hx2 => h.disjoint' hx1 hx2
  have hX₂A : ∀ x, x ∈ (X₂ ∩ B) → x ∉ A := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    exact hd' x hx.2
  have hX₁B : ∀ x, x ∈ (X₁ ∩ A) → x ∉ B := by
    intro x hx
    simp only [Finset.mem_inter] at hx
    exact hd x hx.2
  have hsetA : ((A \ X) ∪ (B \ X)) ∩ A = A \ (X₁ ∩ A) := by
    have hAX' : A \ X = A \ (X₁ ∩ A) := by
      rw [hXdef, sdiff_union_left A (X₁ ∩ A) (X₂ ∩ B) hX₂A]
    rw [hAX']
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hsetB : ((A \ X) ∪ (B \ X)) ∩ B = B \ (X₂ ∩ B) := by
    have hBX' : B \ X = B \ (X₂ ∩ B) := by
      rw [hXdef, Finset.union_comm, sdiff_union_left B (X₂ ∩ B) (X₁ ∩ A) hX₁B]
    rw [hBX']
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  refine ⟨X, hcardX, ?_⟩
  rw [hkey]
  exact isBipartite_induceFinset_of_anticover (s := (A \ X) ∪ (B \ X)) h
    (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_sdiff] at hx
      rcases hx with h1 | h1
      · exact Finset.mem_union.mpr (Or.inl h1.1)
      · exact Finset.mem_union.mpr (Or.inr h1.1))
    (by rw [hsetA]; exact hgA) (by rw [hsetB]; exact hgB)

/-- The class of `Part 2` restricts to the induced subgraphs of an anticover. -/
theorem OddCyclesDisjoint.of_induceFinset (h : OddCyclesDisjoint G) :
    OddCyclesDisjoint (induceFinset G A) := by
  intro C D hC hD
  exact h C D (IsOddCycle.of_induceFinset hC) (IsOddCycle.of_induceFinset hD)

/-- **The instances compose over an anticomplete decomposition.**  If the vertices of `G` split
anticompletely into `A` and `B`, `G` satisfies `LocIndep k`, and the odd cycles of `G` are pairwise
disjoint, then `G` is the union of a bipartite graph and at most `k + k` vertices.  The local
hypothesis restricts to the two sides by `JSPProblem.Residue.LocIndep.of_induceFinset`, and the
class of `Part 2` restricts by `OddCyclesDisjoint.of_induceFinset`. -/
theorem erdos73On_of_anticover (k : ℕ) (hG : LocIndep k G) (hOdd : OddCyclesDisjoint G)
    (h : Anticover G A B) : CloseToBipartite (k + k) G :=
  closeToBipartite_of_anticover h
    (erdos73On_of_disjoint_oddCycles k _ _ _ (LocIndep.of_induceFinset hG A)
      (OddCyclesDisjoint.of_induceFinset hOdd))
    (erdos73On_of_disjoint_oddCycles k _ _ _ (LocIndep.of_induceFinset hG B)
      (OddCyclesDisjoint.of_induceFinset hOdd))

end Anticover
end KFive

end

end JSP90
