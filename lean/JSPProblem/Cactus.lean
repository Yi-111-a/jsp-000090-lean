/-
# JSP-000090 — the ODD CACTUS axis: `LocIndep 1` forces a ONE-vertex transversal

Attack family 28 (round 81).  New module, imported from the root module `JSPProblem.lean`.

## The class

`JSP90.OddCactus G` says that **the odd cycles of `G` form a cactus**: they are *linear* (two
distinct odd cycles meet in at most one vertex) and *two-Helly* (three pairwise meeting odd cycles
have a common vertex, so there is no **ring** of three odd cycles meeting in three distinct
points).  This is a new class for JSP-000090: it mentions only how the odd cycles of `G` intersect
one another, and it *contains* the class of `JSPProblem/Optimal.lean`
(`JSP90.OddCactus.of_oddCyclesDisjoint`).

## What is proved

1. **THE STRUCTURAL LEMMA** (`JSP90.disjoint_of_attach_ne`): two odd cycles that meet a common odd
   cycle at *different* vertices are **disjoint**.  This is the combinatorial core of the class, and
   it is where the two-Helly condition is used.
2. **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1`, WITH THE OPTIMAL CONSTANT `1`**
   (`JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one`, and in the `Erdős73On` form
   `JSP90.erdos73On_oddCactus_one`): `LocIndep 1 G → OddCactus G → CloseToBipartite 1 G`.
   Erdős's hypothesis is used only through the packing bound at `k = 1`, i.e. "every two odd cycles
   meet".  There is **no** bound on the odd girth, **no** degree bound, **no** connectivity
   hypothesis and no decomposition: the only structure used is how the odd cycles intersect.  The
   constant `1` is the smallest possible for a non-bipartite graph, so the `k = 1` value of `f` on
   this class is exactly `1` — against the constant `2` of `JSPProblem/Cover.lean`, whose class
   `ShareCycleEdge` is a different one and which admits the witness `p9`.
3. **A NEW INSTANCE AT EVERY `k`** (`JSP90.erdos73On_oddCactus`), with the constant `k * (k + 1)`:
   a maximum packing of odd cycles has at most `k` members and meets every odd cycle, and the
   *attachment points* of a member — the vertices at which another odd cycle meets it — are at most
   `k` in number, by Part 1 together with the packing bound.
4. **THE REMAINING STATEMENT** (Part 5, stated as a `def` and *not* assumed): `LinearOddCycles G →
   TwoHellyOddCycles G`, the classical *ring* lemma — a ring of three odd cycles gives, by
   concatenating one arc of each of the three cycles, an odd cycle meeting two of them in two
   vertices, contradicting linearity.  Parts 1–4 are proved under the stronger hypothesis
   `OddCactus G`, which is exactly that lemma *assumed*; with it, Parts 1–3 would be available under
   `LinearOddCycles G` alone.  The proof needs a "closing path" generalisation of
   `JSP90.arc_isOddCycle_of_notMem` of `JSPProblem/Chord.lean` (which closes an arc through a single
   *vertex*), since here the concatenation uses three arcs.
-/
import JSPProblem.Cover

namespace JSP90

open Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance instDecidableEqCactus : DecidableEq V := Classical.decEq V

local instance instDecidableIsOddCycleCactus {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ## Part 0 — auxiliary lemmas -/

/-- **`|s.attach| = |s|`.**  `Finset.card_image_of_injOn` applied to `Subtype.val`. -/
theorem card_attach' {α : Type*} (s : Finset α) : s.attach.card = s.card := by
  classical
  have h1 := Finset.card_image_of_injOn (s := s.attach) (f := Subtype.val)
    (Set.injOn_of_injective Subtype.val_injective)
  have h2 : s.attach.image Subtype.val = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
      exact ha ▸ a.2
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach s ⟨x, hx⟩, rfl⟩
  rw [h2] at h1
  exact h1.symm

/-- **A vertex of an intersection witnesses that the intersection is nonempty.** -/
theorem nonempty_of_mem_inter {C D : Finset V} {a : V} (ha : a ∈ C ∩ D) : C ∩ D ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩

/-- A witness in one order is a witness in the other (`a ∈ D ∩ C` gives `a ∈ C ∩ D`). -/
theorem mem_inter_comm' {C D : Finset V} {a : V} (ha : a ∈ D ∩ C) : a ∈ C ∩ D :=
  Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).2, (Finset.mem_inter.mp ha).1⟩

/-- The same, for a witness given in the other order (`a ∈ D ∩ C` gives `C ∩ D ≠ ∅`). -/
theorem nonempty_of_mem_inter_comm {C D : Finset V} {a : V} (ha : a ∈ D ∩ C) : C ∩ D ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp ⟨a, mem_inter_comm' ha⟩

/-- A witness makes a finset nonempty. -/
theorem nonempty_of_mem {α : Type*} {s : Finset α} {x : α} (hx : x ∈ s) : s.Nonempty := ⟨x, hx⟩

/-- A nonempty finset is not empty — the `.mpr` direction of `Finset.nonempty_iff_ne_empty`,
spelled out so that the finset is determined. -/
theorem nonempty_of_ne_empty {α : Type*} {s : Finset α} (h : s ≠ ∅) : s.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr h

/-- An empty finset has no witness. -/
theorem not_nonempty_of_eq_empty {α : Type*} {s : Finset α} (h : s = ∅) : ¬s.Nonempty :=
  fun hn => (Finset.nonempty_iff_ne_empty.mp hn) h

/-- A witness shows a finset is not empty. -/
theorem ne_empty_of_mem {α : Type*} {s : Finset α} {x : α} (hx : x ∈ s) : s ≠ ∅ := by
  intro hs
  rw [hs] at hx
  exact absurd hx (by simp)

/-- **Under `C ∩ D = {a}`, a vertex of the intersection is `a`.** -/
theorem eq_of_mem_inter_eq_singleton {C D : Finset V} {a x : V} (h : C ∩ D = {a}) (hx : x ∈ C ∩ D) :
    x = a :=
  Finset.mem_singleton.mp (h ▸ hx)

/-- **The cardinality of a union of finitely many finsets is at most the sum of the
cardinalities** (`Finset.card_union_le`, by induction on the family). -/
theorem card_le_sum_card_biUnion {C : Finset (Finset V)} {f : Finset V → Finset V} :
    (C.biUnion f).card ≤ ∑ i ∈ C, (f i).card := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 := Finset.card_union_le (f a) (s.biUnion f)
      have h2 := ih
      omega

/-! ## Part 1 — the class: the ODD CACTUS -/

/-- **LINEARITY.**  Two *distinct* odd cycles of `G` meet in at most one vertex.

The `C ≠ D` is essential: for `C = D` the intersection is `C` itself, of at least three vertices. -/
noncomputable def LinearOddCycles (G : SimpleGraph V) : Prop :=
  ∀ C D : Finset V, IsOddCycle G C → IsOddCycle G D → C ≠ D → (C ∩ D).card ≤ 1

/-- **TWO-HELLY.**  Three pairwise meeting odd cycles of `G` have a common vertex; equivalently
there is no **ring** of three odd cycles meeting in three distinct vertices. -/
noncomputable def TwoHellyOddCycles (G : SimpleGraph V) : Prop :=
  ∀ C D E : Finset V, IsOddCycle G C → IsOddCycle G D → IsOddCycle G E →
    C ∩ D ≠ ∅ → D ∩ E ≠ ∅ → E ∩ C ≠ ∅ → ∃ v, v ∈ C ∩ D ∩ E

/-- **THE ODD CACTUS: the odd cycles of `G` are linear and two-Helly.** -/
noncomputable def OddCactus (G : SimpleGraph V) : Prop :=
  LinearOddCycles G ∧ TwoHellyOddCycles G

/-- **Under linearity and a nonempty intersection, the intersection is a single vertex.** -/
theorem LinearOddCycles.eq_singleton_of_mem {C D : Finset V} (h : LinearOddCycles G)
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hne : C ≠ D) {a : V} (ha : a ∈ C ∩ D) :
    C ∩ D = {a} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun y hy => ?_⟩
  have h1 : (C ∩ D).card ≤ 1 := h C D hC hD hne
  exact (Finset.card_le_one_iff.mp h1 ha hy).symm

/-- **THE CLASS OF PART 1 CONTAINS ROUND 39's CLASS.**  `OddCyclesDisjoint G` — any two distinct
odd cycles of `G` are disjoint — implies `OddCactus G`: the intersections have cardinality `0 ≤ 1`,
and three pairwise meeting odd cycles must be equal, so their common intersection is that cycle. -/
theorem OddCactus.of_oddCyclesDisjoint (h : OddCyclesDisjoint G) : OddCactus G := by
  refine ⟨?_, ?_⟩
  · intro C D hC hD hne
    rcases h C D hC hD with h' | h'
    · exact absurd h' hne
    · rw [h']
      simp
  · intro C D E hC hD hE hCD hDE hEC
    have hCDE : C = D := by
      rcases h C D hC hD with h' | h'
      · exact h'
      · exact absurd h' hCD
    have hDEE : D = E := by
      rcases h D E hD hE with h' | h'
      · exact h'
      · exact absurd h' hDE
    obtain ⟨v, hv⟩ := hC.nonempty
    have hCD' : v ∈ C ∩ D := Finset.mem_inter.mpr ⟨hv, by rw [← hCDE]; exact hv⟩
    have hE' : v ∈ E := by
      rw [← hDEE, ← hCDE]
      exact hv
    exact ⟨v, Finset.mem_inter.mpr ⟨hCD', hE'⟩⟩

/-- **THREE ELEMENT MEMBERSHIPS GIVE A WITNESS IN THE TRIPLE INTERSECTION**, and conversely a witness
in the triple intersection lies in each of the three finsets.

Both are phrased with *element* memberships, because the finset `C ∩ D ∩ E` built here carries the
classical `DecidableEq` of this section: a statement mentioning it directly would not be defeq to
one built in the finite section of `JSPProblem/Sun.lean`, where the computable instance is in
scope. -/
theorem exists_mem_inter3 {C D E : Finset V} {v : V} (h1 : v ∈ C) (h2 : v ∈ D) (h3 : v ∈ E) :
    ∃ w, w ∈ C ∩ D ∩ E :=
  ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h1, h2⟩, h3⟩⟩

/-- A witness in the triple intersection lies in each of the three finsets. -/
theorem mem_of_mem_inter3 {C D E : Finset V} {v : V} (h : v ∈ C ∩ D ∩ E) : v ∈ C ∧ v ∈ D ∧ v ∈ E :=
  ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1,
    (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2,
    (Finset.mem_inter.mp h).2⟩

/-- **TWO-HELLY APPLIED TO THREE PAIRWISE MEETING FINSETS**, each pair witnessed separately — the
instance-free form used by the finite section of `JSPProblem/Sun.lean`. -/
theorem twoHelly_of_three_ne {C D E : Finset V} (h : TwoHellyOddCycles G) (hC : IsOddCycle G C)
    (hD : IsOddCycle G D) (hE : IsOddCycle G E) {x y z : V} (hx1 : x ∈ C) (hx2 : x ∈ D)
    (hy1 : y ∈ D) (hy2 : y ∈ E) (hz1 : z ∈ E) (hz2 : z ∈ C) : ∃ v, v ∈ C ∩ D ∩ E :=
  h C D E hC hD hE
    (ne_empty_of_mem (Finset.mem_inter.mpr ⟨hx1, hx2⟩))
    (ne_empty_of_mem (Finset.mem_inter.mpr ⟨hy1, hy2⟩))
    (ne_empty_of_mem (Finset.mem_inter.mpr ⟨hz1, hz2⟩))

/-- **AN ODD CYCLE AVOIDING A VERTEX SURVIVES IN THE RESIDUE.**  Phrased existentially, so that it
can be used from the finite section of `JSPProblem/Sun.lean`, where the computable `DecidableEq` is
in scope and the finset `C ∩ {v}` is not defeq to the one built here. -/
theorem exists_oddCycle_deleteFinset {C : Finset V} (hC : IsOddCycle G C) {v : V} (hv : v ∉ C) :
    ∃ D : Finset V, IsOddCycle (deleteFinset G {v}) D := by
  refine ⟨C, IsOddCycle.delete_avoiding hC ?_⟩
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  rw [Finset.mem_inter] at hx
  have hxv : x = v := Finset.mem_singleton.mp hx.2
  exact hv (by rw [← hxv]; exact hx.1)

/-- **TWO DISTINCT COMMON WITNESSES REFUTE LINEARITY.**  This is the statement of the class that is
*instance-free* in its second argument, and it is what the finite section of
`JSPProblem/Sun.lean` uses. -/
theorem not_linear_of_two_mem {C D : Finset V} (h : LinearOddCycles G) (hC : IsOddCycle G C)
    (hD : IsOddCycle G D) (hne : C ≠ D) {x y : V} (hx1 : x ∈ C) (hx2 : x ∈ D) (hy1 : y ∈ C)
    (hy2 : y ∈ D) (hxy : x ≠ y) : False := by
  have h1 := h C D hC hD hne
  have h2 := Finset.card_le_one_iff.mp h1 (Finset.mem_inter.mpr ⟨hx1, hx2⟩)
    (Finset.mem_inter.mpr ⟨hy1, hy2⟩)
  exact hxy h2

/-! ## Part 2 — the structural lemma -/

/-- **TWO ODD CYCLES THAT MEET A COMMON ODD CYCLE AT *DIFFERENT* VERTICES ARE DISJOINT.**

This is the content of the ODD CACTUS class.  Suppose `D` meets `C` at `a`, `E` meets `C` at
`a' ≠ a`, and `D`, `E` meet at `b`.  Linearity gives `C ∩ D = {a}` and `C ∩ E = {a'}`, so `a ∉ E`
(else `C ∩ E` would have two elements) and hence `C ∩ D ∩ E = ∅`.  But `C`, `D`, `E` are three
pairwise meeting odd cycles, contradicting two-Helly. -/
theorem disjoint_of_attach_ne (hc : OddCactus G) {C D E : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hE : IsOddCycle G E)
    (hDC : D ≠ C) (hEC : E ≠ C) {a a' : V} (ha : a ∈ D ∩ C) (ha' : a' ∈ E ∩ C)
    (haa' : a ≠ a') : D ∩ E = ∅ := by
  classical
  by_contra hcon
  obtain ⟨b, hb⟩ := nonempty_of_ne_empty hcon
  have haC : a ∈ C := (Finset.mem_inter.mp ha).2
  have ha'E : a' ∈ E := (Finset.mem_inter.mp ha').1
  have hCD : C ∩ D = {a} := hc.1.eq_singleton_of_mem hC hD (Ne.symm hDC) (mem_inter_comm' ha)
  have hCE : C ∩ E = {a'} := hc.1.eq_singleton_of_mem hC hE (Ne.symm hEC) (mem_inter_comm' ha')
  have haE : a ∉ E := by
    intro haE
    have h1 : a = a' := Finset.mem_singleton.mp (hCE ▸ Finset.mem_inter.mpr ⟨haC, haE⟩)
    exact haa' h1
  have htri : C ∩ D ∩ E = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    rcases Finset.mem_inter.mp hx with hxCE
    have h1 : x = a := eq_of_mem_inter_eq_singleton hCD hxCE.1
    exact haE (h1 ▸ hxCE.2)
  have hmeetCD : C ∩ D ≠ ∅ := ne_empty_of_mem (mem_inter_comm' ha)
  have hmeetDE : D ∩ E ≠ ∅ := ne_empty_of_mem hb
  have hmeetEC : E ∩ C ≠ ∅ := ne_empty_of_mem ha'
  obtain ⟨v, hv⟩ := hc.2 C D E hC hD hE hmeetCD hmeetDE hmeetEC
  exact absurd (nonempty_of_mem hv) (not_nonempty_of_eq_empty htri)

/-! ## Part 3 — the `k = 1` level, with the optimal constant `1` -/

/-- **IN AN ODD CACTUS WITH `LocIndep 1`, ALL THE ODD CYCLES HAVE A COMMON VERTEX.** -/
theorem exists_commonVertex_oddCactus_of_locIndep_one (hG : LocIndep 1 G) (hc : OddCactus G)
    (hodd : ∃ C : Finset V, IsOddCycle G C) :
    ∃ a : V, ∀ D : Finset V, IsOddCycle G D → a ∈ D := by
  classical
  obtain ⟨C, hC⟩ := hodd
  by_cases hone : ∀ D E : Finset V, IsOddCycle G D → IsOddCycle G E → D = E
  · obtain ⟨a, ha⟩ := hC.nonempty
    refine ⟨a, fun D hD => ?_⟩
    have hDC : D = C := hone D C hD hC
    rw [hDC]
    exact ha
  · push_neg at hone
    obtain ⟨D, E, hD, hE, hneDE⟩ := hone
    -- a pair of distinct odd cycles
    obtain ⟨P, Q, hP, hQ, hPQ⟩ : ∃ P Q : Finset V, IsOddCycle G P ∧ IsOddCycle G Q ∧ P ≠ Q := by
      by_cases h : C = D
      · exact ⟨D, E, hD, hE, hneDE⟩
      · exact ⟨C, D, hC, hD, h⟩
    obtain ⟨a, ha⟩ := nonempty_of_ne_empty (inter_oddCycle_of_locIndep_one hG hP hQ)
    have hPQ : P ∩ Q = {a} := hc.1.eq_singleton_of_mem hP hQ hPQ ha
    have hall : ∀ X : Finset V, IsOddCycle G X → a ∈ X := by
      intro X hX
      by_contra hna
      have hXP : X ≠ P := by
        intro h
        subst h
        exact hna (Finset.mem_inter.mp ha).1
      have hXQ : X ≠ Q := by
        intro h
        subst h
        exact hna (Finset.mem_inter.mp ha).2
      have htri : P ∩ Q ∩ X = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun y hyX => ?_
        rcases Finset.mem_inter.mp hyX with hyPX
        have h1 : y = a := eq_of_mem_inter_eq_singleton hPQ hyPX.1
        exact hna (h1 ▸ hyPX.2)
      obtain ⟨b, hb⟩ := nonempty_of_ne_empty
        (inter_oddCycle_of_locIndep_one hG hQ hX)
      have hmeetPQ : P ∩ Q ≠ ∅ := ne_empty_of_mem ha
      have hmeetQX : Q ∩ X ≠ ∅ := ne_empty_of_mem hb
      have hmeetXP : X ∩ P ≠ ∅ := inter_oddCycle_of_locIndep_one hG hX hP
      obtain ⟨v, hv⟩ := hc.2 P Q X hP hQ hX hmeetPQ hmeetQX hmeetXP
      exact absurd (nonempty_of_mem hv) (not_nonempty_of_eq_empty htri)
    exact ⟨a, hall⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1`, WITH THE OPTIMAL CONSTANT `1`.**

`LocIndep 1 G` (every subgraph of `G` carries an independent set of size `≥ (|V| - 1) / 2`) and
`OddCactus G` force `G` to be **one** vertex away from bipartite.

There is no bound on the odd girth, no bound on the degrees, no connectivity hypothesis and no
decomposition hypothesis: the only structure used is how the odd cycles of `G` intersect.  Erdős's
hypothesis enters solely through the packing bound at `k = 1`, i.e. "every two odd cycles meet"
(`JSP90.inter_oddCycle_of_locIndep_one`). -/
theorem closeToBipartite_one_of_oddCactus_of_locIndep_one (hG : LocIndep 1 G)
    (hc : OddCactus G) : CloseToBipartite 1 G := by
  classical
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨a, ha⟩ := exists_commonVertex_oddCactus_of_locIndep_one hG hc hodd
    refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨{a}, by simp, fun D hD => ?_⟩
    exact ne_empty_of_mem (Finset.mem_inter.mpr ⟨ha D hD, Finset.mem_singleton.mpr rfl⟩)
  · refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨∅, by simp, fun D hD => ?_⟩
    exact absurd ⟨D, hD⟩ hodd

/-- **THE `k = 1` LEVEL OF PART 3 IN THE `Erdős73On` FORM: A NEW INSTANCE OF THE HEADLINE
THEOREM.**  For every finite graph on which every subgraph carries an independent set of size
`≥ (|V| - 1) / 2` and whose odd cycles form a cactus, deleting **one** vertex suffices to make the
graph bipartite. -/
theorem erdos73On_oddCactus_one :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → OddCactus G →
      CloseToBipartite 1 G :=
  fun _ _ _ hG hc => closeToBipartite_one_of_oddCactus_of_locIndep_one hG hc

/-! ## Part 4 — every `k`: the constant `k * (k + 1)` -/

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, AT EVERY `k`, WITH THE CONSTANT `k * (k + 1)`.**

`LocIndep k G → OddCactus G → CloseToBipartite (k * (k + 1)) G`.

The argument.  A maximum packing `𝒞` of odd cycles has at most `k` members and meets every odd
cycle of `G`.  Fix a member `C`.  Its **attachment points** — the vertices at which another odd
cycle meets it — are the image, under `D ↦` (the unique point of `C ∩ D`), of the family of odd
cycles `≠ C` meeting `C`; and the odd cycles attaching at *different* points are **disjoint**
(Part 2), so the number of attachment points is the cardinality of a packing and hence at most `k`.
The union, over the `|𝒞| ≤ k` members of the maximum packing, of their attachment points together
with one vertex of each member is therefore an odd cycle transversal of size at most `k * k + k`. -/
theorem erdos73On_oddCactus (k : ℕ) (hG : LocIndep k G) (hc : OddCactus G) :
    CloseToBipartite (k * (k + 1)) G := by
  classical
  obtain ⟨𝒞, h𝒞, hmax⟩ := exists_maxCard_oddCycleFamily (G := G)
  have hr : 𝒞.card ≤ k := hG.oddCycleFamily_card_le h𝒞
  have hhit : ∀ D : Finset V, IsOddCycle G D → ∃ i ∈ 𝒞, D ∩ i ≠ ∅ := by
    intro D hD
    have h1 := hitsOddCycles_of_maxCardFamily h𝒞 hmax D hD
    obtain ⟨x, hx⟩ := nonempty_of_ne_empty h1
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
    exact ⟨i, hi, ne_empty_of_mem (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxi⟩)⟩
  -- one vertex per member of the maximum packing
  have hneC : ∀ i ∈ 𝒞, (i : Finset V).Nonempty := fun i hi => (h𝒞.2 i hi).nonempty
  set f0 : {i // i ∈ 𝒞} → V :=
    fun i => @Classical.choose V (fun x => x ∈ (i : Finset V)) (hneC i.1 i.2) with hf0def
  have hf0mem : ∀ i : {i // i ∈ 𝒞}, f0 i ∈ (i : Finset V) := fun i => Classical.choose_spec _
  have hf0inj : Function.Injective f0 := by
    intro a b hab
    by_cases hEq : (a.1 : Finset V) = b.1
    · exact Subtype.ext hEq
    · have hdisj : Disjoint (a.1 : Finset V) b.1 :=
        Finset.disjoint_iff_inter_eq_empty.mpr (h𝒞.1 a.1 a.2 b.1 b.2 hEq)
      exact absurd (hab ▸ hf0mem b) (Finset.disjoint_left.mp hdisj (hf0mem a))
  set X0 : Finset V := 𝒞.attach.image f0 with hX0def
  have hX0card : X0.card ≤ k := by
    have h1 := Finset.card_image_of_injOn (s := 𝒞.attach) (f := f0)
      (Set.injOn_of_injective hf0inj)
    rw [card_attach'] at h1
    exact le_trans (le_of_eq h1) hr
  -- the odd cycles `≠ i` meeting `i`, and the attachment points of `i`
  set 𝒟 : Finset V → Finset (Finset V) := fun i =>
    (Finset.univ : Finset (Finset V)).filter
      (fun D => IsOddCycle G D ∧ D ≠ i ∧ D ∩ i ≠ ∅) with h𝒟def
  have h𝒟mem : ∀ i (D : Finset V), D ∈ 𝒟 i ↔ IsOddCycle G D ∧ D ≠ i ∧ D ∩ i ≠ ∅ := by
    intro i D
    rw [h𝒟def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have h𝒟ne : ∀ (i D : Finset V) (hD : IsOddCycle G D) (hne : D ≠ i) (hmeet : D ∩ i ≠ ∅),
      D ∈ 𝒟 i := by
    intro i D hD hne hmeet
    rw [h𝒟mem]
    exact ⟨hD, hne, hmeet⟩
  have h𝒟oddc : ∀ (i D : Finset V) (hD : D ∈ 𝒟 i), IsOddCycle G D := by
    intro i D hD
    exact (h𝒟mem i D).mp hD |>.1
  have h𝒟ne' : ∀ (i D : Finset V) (hD : D ∈ 𝒟 i), D ≠ i := by
    intro i D hD
    exact (h𝒟mem i D).mp hD |>.2.1
  set f1 : ∀ i : Finset V, {D // D ∈ 𝒟 i} → V := fun i D =>
    @Classical.choose V (fun x => x ∈ D.1 ∩ i)
      (nonempty_of_ne_empty ((h𝒟mem i D.1).mp D.2).2.2) with hf1def
  have hf1mem : ∀ (i : Finset V) (D : {D // D ∈ 𝒟 i}), f1 i D ∈ D.1 ∩ i := fun i D =>
    Classical.choose_spec _
  set Y : Finset V → Finset V := fun i => (𝒟 i).attach.image (f1 i) with hYdef
  have hYsub : ∀ i : Finset V, Y i ⊆ i := by
    intro i x hx
    obtain ⟨D, _, hmap⟩ := Finset.mem_image.mp hx
    rw [← hmap]
    exact (Finset.mem_inter.mp (hf1mem i D)).2
  have hYcard : ∀ (i : Finset V) (hi : IsOddCycle G i), (Y i).card ≤ k := by
    intro i hi
    have hex : ∀ a ∈ Y i, ∃ D : Finset V, D ∈ 𝒟 i ∧ a ∈ D := by
      intro a ha
      obtain ⟨D, _, hmap⟩ := Finset.mem_image.mp ha
      exact ⟨D.1, D.2, by rw [← hmap]; exact (Finset.mem_inter.mp (hf1mem i D)).1⟩
    set gr : V → Finset V := fun v => if h : v ∈ Y i then Classical.choose (hex v h) else ∅ with hgrdef
    have hgrmem : ∀ a ∈ Y i, gr a ∈ 𝒟 i ∧ a ∈ gr a := by
      intro a ha
      have hgr : gr a = Classical.choose (hex a ha) := by
        simp only [hgrdef]
        rw [dif_pos ha]
      rw [hgr]
      exact Classical.choose_spec (hex a ha : ∃ D : Finset V, D ∈ 𝒟 i ∧ a ∈ D)
    have hgrne : ∀ a ∈ Y i, gr a ≠ i := fun a ha => h𝒟ne' i (gr a) ((hgrmem a ha).1)
    have hgrinj : Set.InjOn gr (Y i) := by
      intro a ha b hb hab
      by_contra hne
      have h1 : (gr a ∩ i).card ≤ 1 :=
        hc.1 (gr a) i (h𝒟oddc i (gr a) ((hgrmem a ha).1)) hi (hgrne a ha)
      have hsub : ({a, b} : Finset V) ⊆ gr a ∩ i := by
        intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hxb
        · rw [hxa]
          exact Finset.mem_inter.mpr ⟨(hgrmem a ha).2, hYsub i ha⟩
        · rw [Finset.mem_singleton.mp hxb, hab]
          exact Finset.mem_inter.mpr ⟨(hgrmem b hb).2, hYsub i hb⟩
      have hcard2 : ({a, b} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
          Finset.card_singleton]
      have h3 := Finset.card_le_card hsub
      rw [hcard2] at h3
      exact absurd h1 (fun hle => by omega)
    have hfam : IsOddCycleFamily (G := G) ((Y i).image gr) := by
      refine ⟨?_, ?_⟩
      · intro X hX Y' hY' hne
        obtain ⟨a, ha, hX⟩ := Finset.mem_image.mp hX
        obtain ⟨b, hb, hY'⟩ := Finset.mem_image.mp hY'
        rw [← hX, ← hY'] at hne
        rw [← hX, ← hY']
        have hneab : a ≠ b := by
          rintro rfl
          exact hne rfl
        exact disjoint_of_attach_ne (C := i) (D := gr a) (E := gr b) hc hi
          (h𝒟oddc i (gr a) ((hgrmem a ha).1)) (h𝒟oddc i (gr b) ((hgrmem b hb).1))
          (hgrne a ha) (hgrne b hb)
          (Finset.mem_inter.mpr ⟨(hgrmem a ha).2, hYsub i ha⟩)
          (Finset.mem_inter.mpr ⟨(hgrmem b hb).2, hYsub i hb⟩) hneab
      · intro X hX
        obtain ⟨a, ha, hX'⟩ := Finset.mem_image.mp hX
        rw [← hX']
        exact h𝒟oddc i (gr a) ((hgrmem a ha).1)
    have h1 : ((Y i).image gr).card ≤ k := hG.oddCycleFamily_card_le hfam
    have h2 : (Y i).card ≤ ((Y i).image gr).card := by
      rw [Finset.card_image_of_injOn hgrinj]
    exact le_trans h2 h1
  -- the transversal
  refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨X0 ∪ 𝒞.biUnion Y, ?_, ?_⟩
  · have h2 : (𝒞.biUnion Y).card ≤ ∑ i ∈ 𝒞, (Y i).card := card_le_sum_card_biUnion
    have h3 : (∑ i ∈ 𝒞, (Y i).card) ≤ 𝒞.card * k := by
      have hle : (∑ i ∈ 𝒞, (Y i).card) ≤ ∑ _i ∈ 𝒞, (k : ℕ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact hYcard i (h𝒞.2 i hi)
      rw [Finset.sum_const_nat (s := 𝒞) (f := fun _ : Finset V => k) (m := k) (by
        intro _ _
        rfl)] at hle
      exact hle
    calc (X0 ∪ 𝒞.biUnion Y).card ≤ X0.card + (𝒞.biUnion Y).card := Finset.card_union_le _ _
      _ ≤ k + (∑ i ∈ 𝒞, (Y i).card) := Nat.add_le_add hX0card h2
      _ ≤ k + 𝒞.card * k := Nat.add_le_add_left h3 k
      _ ≤ k + k * k := Nat.add_le_add_left (Nat.mul_le_mul_right k hr) k
      _ = k * (k + 1) := (Nat.add_comm k (k * k)).trans (Nat.mul_succ k k)
  · intro D hD
    obtain ⟨i, hi, hDi⟩ := hhit D hD
    by_cases hDi' : D = i
    · refine ne_empty_of_mem (x := f0 ⟨i, hi⟩) ?_
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [hDi']
        exact hf0mem ⟨i, hi⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f0 (Finset.mem_attach 𝒞 ⟨i, hi⟩))
    · have hDin : D ∈ 𝒟 i := h𝒟ne i D hD hDi' hDi
      refine ne_empty_of_mem (x := f1 i ⟨D, hDin⟩) ?_
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact (Finset.mem_inter.mp (hf1mem i ⟨D, hDin⟩)).1
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi,
          Finset.mem_image_of_mem (f1 i) (Finset.mem_attach (𝒟 i) ⟨D, hDin⟩)⟩)

/-! ## Part 5 — the remaining statement, isolated and *not* assumed -/

/-- **THE RING LEMMA, AS A STATEMENT.**  In a graph whose odd cycles are linear, three pairwise
meeting odd cycles have a common vertex.

This is the classical argument: a ring `C`, `D`, `E` meeting pairwise in three distinct vertices
`a`, `b`, `c` gives — by concatenating one arc of each of the three cycles — an **odd** cycle, and
that cycle meets `C` in the two vertices `a` and `c`, contradicting linearity.  The parity step is
elementary: the two arcs of an odd cycle between two vertices have opposite parity.

It is a `def`, so nothing above uses it: Parts 1–4 are proved under the stronger hypothesis
`OddCactus G`, which is exactly this lemma *assumed*.  Proving it needs a "closing path" version of
`JSP90.arc_isOddCycle_of_notMem` of `JSPProblem/Chord.lean` (which closes an arc through a single
*vertex*), since here the concatenation uses three arcs; that was not attempted this round. -/
noncomputable def LinearRing (G : SimpleGraph V) : Prop :=
  ∀ C D E : Finset V, IsOddCycle G C → IsOddCycle G D → IsOddCycle G E →
    C ∩ D ≠ ∅ → D ∩ E ≠ ∅ → E ∩ C ≠ ∅ → C ∩ D ∩ E ≠ ∅

/-- **NO RING IS TWO-HELLY.** -/
theorem twoHelly_of_linearRing (h : LinearRing G) : TwoHellyOddCycles G := by
  intro C D E hC hD hE hCD hDE hEC
  obtain ⟨v, hv⟩ := nonempty_of_ne_empty (h C D E hC hD hE hCD hDE hEC)
  exact ⟨v, hv⟩

/-- **A LINEAR GRAPH WITH NO RING IS AN ODD CACTUS.**  This is the formal form of "the odd cycles
of `G` form a cactus", and it isolates the single missing implication
(`LinearOddCycles G → LinearRing G`) needed to state Parts 1–3 with the weaker hypothesis
`LinearOddCycles G`. -/
theorem oddCactus_iff (h : LinearOddCycles G) (hr : LinearRing G) : OddCactus G :=
  ⟨h, twoHelly_of_linearRing hr⟩

end

end JSP90
