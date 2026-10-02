/- 
# JSP-000090 — `JSPProblem/TwoAttach.lean`: **the pick-free two-attachment cover**, the
# **machine-checked global target** `TwoAttachCoverExists`, and the **exact cost of a cover**

This is round 115 of the attack on `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
single statement behind `jsp_000090_main` (`JSPProblem/Transversal.lean`
`erdos73_of_erdosPosa`).  `discovery/JSP-000090/policy.json` of round 112 named two concrete next
steps; this file delivers the second of them — *the cover statement itself, written down in Lean* —
in its strongest available form, and settles two questions about the cover route.

## Part 1 — the two-attachment cover **without** a choice function

`JSPProblem/CPathSkip.lean` states the two-attachment cover `TwoAttachCover G 𝒞 pick`: a family `𝒞`
of nonempty vertex sets, a vertex `pick X` picked in each member, and the statement that **every odd
cycle of `G` meets some member in at least two vertices**.  The pick is not used by the counting
argument, and demanding it makes the cover statement awkward to quantify over (one has to produce a
*total* function `Finset V → V`, which does not exist when `V` is empty).  `TwoAttachCover'` here
drops it:

* **`JSP90.exists_oneSidedDeletion`** — **A FAMILY OF NONEMPTY SETS HAS A ONE-SIDED DELETION SET.**
  For a finite family `𝒞` of nonempty sets there is a set `U` with `|U| ≤ ∑ X ∈ 𝒞, (|X| - 1)` and
  `|X \ U| ≤ 1` for every `X ∈ 𝒞`.  The induction on `𝒞` spares one vertex of each member.  **No
  cycle, no adjacency and no graph occurs in this statement**;
* **`JSP90.exists_twoAttachDeletion`** — that lemma applied to a two-attachment cover;
* **`JSP90.hitsOddCycles_of_twoAttachCover'`** and **`JSP90.closeToBipartite_of_twoAttachCover'`** —
  the transversal: the deletion set of a cover meets every odd cycle (two of its vertices lie in
  some `X ∈ 𝒞`, and at most one of them is deleted), so `CloseToBipartite (∑ |X| - 1) G`;
* **`JSP90.closeToBipartite_of_twoAttachCover'_bounded`** — the same with `ℓ` vertices per member
  and `q` members: `CloseToBipartite (ℓ * q) G`.  **This is the Erdős–Pósa shape** (one unit per
  member of an `r`-sized object, as in `LocIndep.oddCycleFamily_card_le`);
* **`JSP90.erdos73On_of_twoAttachCover'`** — again a **new instance of the headline theorem**, with a
  constant independent of Erdős's local parameter `k`.

## Part 2 — **THE MACHINE-CHECKED GLOBAL TARGET**

`JSP90.TwoAttachCoverExists r ℓ q` is the statement named by round 112's blocker, written down in
Lean: *for every graph whose odd cycle packings all have at most `r` members there is a
two-attachment cover with at most `q` members, each of at most `ℓ` vertices.*  It is a `def`, so
nothing is assumed and no placeholder occurs:

* **`JSP90.oddCycleErdosPosa_of_twoAttachCoverExists`** — `TwoAttachCoverExists r ℓ q` implies
  `OddCycleErdosPosa r`, with the explicit constant `ℓ * q`;
* **`JSP90.erdos73_of_twoAttachCoverExists`** — hence **`∀ k, Erdős73 k`**, i.e. the whole of Erdős
  Problem #73 and therefore `jsp_000090_main`, follows from `∀ ℓ q, ∀ r, TwoAttachCoverExists r ℓ q`.

So the residual difficulty of JSP-000090 is now **one statement of a combinatorial existence kind**,
and the classical constant of Erdős #73 would follow from it with `m = ℓ · q`.

## Part 3 — a cover whose members are **odd cycles** loses a factor 2

The most attractive cover is the family of odd cycles themselves: `JSP90.TwoAttachPacking` is a
family of pairwise vertex-disjoint odd cycles every odd cycle of `G` meets twice.  On the sharp
witness this is available and it is **exactly twice as expensive as necessary**:

* **`JSP90.twoAttachPacking_triangles`** — the `k` triangles of `kTriangles k` **are** a two-attachment
  packing (they are disjoint odd cycles, and every odd cycle of `kTriangles k` is one of them);
* **`JSP90.sum_card_sub_one_tri`** and **`JSP90.packing_cover_cost_two_of_kTriangles`** — the
  triangles cost `∑ (|X| - 1) = 2 * k`, while `k` is enough and nothing below `k` works.

So the members of a cover **must be allowed to be vertex sets that are not odd cycles** — which is
why `TwoAttachCover'` is stated for arbitrary nonempty vertex sets, and why Part 4 uses two-vertex
sets rather than triangles.

## Part 4 — the minimum cost of a cover is **exactly the optimum** on the sharp witness

* `JSP90.triPair`, `JSP90.triPairCover`, `JSP90.twoAttachCover'_triPairs` — the family of the
  *two-vertex* sets `{0, 1} × {i}`, one per triangle, is a two-attachment cover of `kTriangles k`
  of cost **exactly `k`** (`JSP90.sum_card_sub_one_triPairs`);
* **`JSP90.cover_cost_ge_of_kTriangles`** — **no cover of `kTriangles k` costs less than `k`**: the
  deletion set of a cover meets all `k` pairwise disjoint triangles;
* **`JSP90.cover_cost_min_kTriangles`** — the two together: the **minimum cost of a two-attachment
  cover of `kTriangles k` is exactly `k`**, which is also the odd cycle transversal number of
  `kTriangles k` (`JSP90.closeToBipartite_iff`);
* **`JSP90.cover_cost_kTriangles_is_optimal`** — hence the cover theorem of Part 1 is **optimal in
  constant** on the family that makes the constant of Erdős #73 large.

That is the strongest possible statement about the cover *method*: on the sharp witness it loses
nothing.  What is missing is only the *existence* of a small cover.

## What is *not* proved

`jsp_000090_main` is still not declared and `JSP90.OddCycleErdosPosa r` is unchanged:
`TwoAttachCoverExists` is **stated**, not proved.  What is missing is the combinatorial content — the
`𝒞` has to be built, with `|𝒞| ≤ q` and `|X| ≤ ℓ` depending only on `r`, for a graph of odd cycle
packing number `r`.  Note also the obstruction recorded in round 114: the one-attachment odd cycles
of `JSPProblem/CPathSkip.lean` (`JSP90.oneAttach_of_isCPath_return`) meet a candidate cover in
exactly one vertex and have to be absorbed by a 2-cut first, and that absorption is bounded by
nothing in this file.

## Toolchain notes

* `Finset.induction_on` produces the `insert` case as `insert X 𝒞 hXnotin ih`, and **the hypothesis
  `hc` is reverted into the motive**, so the induction hypothesis is a *function* of the cover and
  the case hypothesis is the cover of `insert X 𝒞`; `Finset.sum_insert` with all arguments given is
  used to close the sum;
* **a `have` with an explicit type is needed before any `hc.1 Y (… membership …)`**: `hc.1 Y`
  expects `Y ∈ 𝒞` (the *smaller* family of `insert`'s first argument) and Lean will happily unify
  `insert X ?s` with the rigid variable `𝒞` by setting `?s := insert X 𝒞`, producing the nonsense
  type `Y ∈ insert X (insert X 𝒞)` — see `mem_insert_family`, which is stated with the inserted
  member explicit and must be applied through a `have`;
* `Finset.DisjointFamily` of `JSPProblem/Packing.lean` is `X ∩ Y = ∅` **with the `DecidableEq`
  instance of that file baked in**, so a statement of this file about `∩` needs a local instance
  declared in the same anonymous style (`local instance : DecidableEq V := Classical.decEq V`),
  otherwise `rw` and `Finset.card_eq_zero.mpr` fail on `Inter` instance mismatches — the same reason
  the `Fin 3 × Fin k` instances of `JSPProblem/Optimal.lean` are reproduced verbatim here;
* `Finset.card_sdiff : #(t \ s) = #t - #(s ∩ t)` is **not** `#t - #s`; `Finset.inter_eq_self` does not
  exist in this Mathlib, and neither does `Finset.not_mem_empty`.  The deletion set of Part 1 is
  therefore written with `X.erase p` and `Finset.card_erase_of_mem`, and the inverse membership
  statements use `Finset.mem_erase (s := X) (b := p)` with both arguments explicit — `.mp` on
  `Finset.mem_erase` with all implicits left to unification misfires on the `∉` side;
* `Finset.mem_image` has the *equation* on the right (`∃ b ∈ s, f b = a`), so `mem_triPair` must be
  stated as `∃ a, (…, i) = p`, and `Finset.sum_image` (not `sum_image'`) is the version to use, with
  the injectivity hypothesis `Set.InjOn g ((Finset.univ : Finset (Fin k)) : Set (Fin k))` — which is
  **not** the same term as `Set.InjOn g Set.univ`;
* `two-element `Finset`s of `Fin 3 × Fin k` are handled best by writing them literally
  (`{(⟨0, by decide⟩, i), (⟨1, by decide⟩, i)}`) and letting `simp [triPair]` compute the card;
* `closeToBipartite_iff (k := k) (m := k - 1)` is **not** refutable by `omega` at `k = 0`, because
  `k - 1 = 0` there: the optimality statements must quantify `∀ m, m < k`, not `k - 1`.
-/

import JSPProblem.CPathPair
import JSPProblem.Optimal

namespace JSP90

open Finset Fintype

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

noncomputable section

local instance instDecidableEqTwoAttachV : DecidableEq V := Classical.decEq V

local instance instDecidableEqTwoAttachProd : DecidableEq (Fin 3 × Fin k) := Classical.decEq _

local instance instDecidableEqTwoAttachProdFinset : DecidableEq (Finset (Fin 3 × Fin k)) :=
  Classical.decEq _

local instance instDecidableEqTwoAttachProdFinsetFinset :
    DecidableEq (Finset (Finset (Fin 3 × Fin k))) := Classical.decEq _

/-! ### Part 1 — the two-attachment cover, without a choice function -/

section Cover'

variable {𝒞 : Finset (Finset V)}

/-- **`𝒞` IS A TWO-ATTACHMENT COVER OF `G`, IN PICK-FREE FORM.**  Every member of `𝒞` is nonempty
and every odd cycle of `G` meets some member of `𝒞` in at least two vertices.

This is `JSP90.TwoAttachCover` of `JSPProblem/CPathSkip.lean` with the choice function `pick`
forgotten: the counting argument of the cover theorem never uses it, and dropping it makes the
statement quantify over families without producing a total function `Finset V → V` (which does not
exist when `V` is empty). -/
def TwoAttachCover' (G : SimpleGraph V) (𝒞 : Finset (Finset V)) : Prop :=
  (∀ X ∈ 𝒞, X.Nonempty) ∧ (∀ D : Finset V, IsOddCycle G D → ∃ X ∈ 𝒞, 2 ≤ (D ∩ X).card)

/-- **MEMBERSHIP IN AN INSERTED FAMILY**, with the inserted member given explicitly (the
`DecidableEq` instance of the family is then unambiguous). -/
theorem mem_insert_family {C : Finset (Finset V)} {X Y : Finset V} (hY : Y ∈ C) :
    Y ∈ insert X C :=
  (Finset.mem_insert (a := Y) (b := X) (s := C)).2 (Or.inr hY)

/-- The round-112 cover, in pick-free form: a member containing the picked vertex is nonempty, and
the attachment statement is unchanged. -/
theorem TwoAttachCover.to_cover' {pick : Finset V → V} (hc : TwoAttachCover G 𝒞 pick) :
    TwoAttachCover' G 𝒞 :=
  ⟨fun X hX => ⟨pick X, hc.1 X hX⟩, hc.2⟩

/-- **A FAMILY OF NONEMPTY SETS HAS A ONE-SIDED DELETION SET.**

Let `𝒞` be a finite family of nonempty vertex sets.  There is a set `U` of at most
`∑ X ∈ 𝒞, (|X| - 1)` vertices such that **`𝒞` keeps at most one vertex of each of its members**,
i.e. `|X \ U| ≤ 1` for every `X ∈ 𝒞`.

The induction on `𝒞` spares one vertex `p` of each member `X` (so `U ∪ (X \ {p})` leaves at most
`{p}` of `X` deleted) and never deletes more than it has paid for.  **No cycle, no adjacency and no
`G` occur in this statement**: it is a fact about families of sets, which is why
`closeToBipartite_of_twoAttachCover'` below needs nothing else. -/
theorem exists_oneSidedDeletion (hne : ∀ X ∈ 𝒞, X.Nonempty) :
    ∃ U : Finset V, U.card ≤ ∑ X ∈ 𝒞, (X.card - 1) ∧ ∀ X ∈ 𝒞, (X \ U).card ≤ 1 := by
  classical
  induction 𝒞 using Finset.induction_on with
  | empty =>
      refine ⟨∅, by simp, ?_⟩
      intro X hX
      simp at hX
  | @insert X 𝒞 hXnotin ih =>
      have hne' : ∀ Y ∈ 𝒞, Y.Nonempty := fun Y hY => hne Y (mem_insert_family (X := X) hY)
      obtain ⟨U, hU, hinv⟩ := ih hne'
      obtain ⟨p, hp⟩ := hne X (Finset.mem_insert_self X 𝒞)
      refine ⟨U ∪ X.erase p, ?_, ?_⟩
      · calc (U ∪ X.erase p).card ≤ U.card + (X.erase p).card := Finset.card_union_le _ _
        _ ≤ (∑ Y ∈ 𝒞, (Y.card - 1)) + (X.card - 1) := by
            rw [Finset.card_erase_of_mem hp]
            exact Nat.add_le_add_right hU _
        _ = ∑ Y ∈ (insert X 𝒞 : Finset (Finset V)), (Y.card - 1) := by
            rw [Finset.sum_insert hXnotin (f := fun Y : Finset V => Y.card - 1)]
            exact Nat.add_comm _ _
      · intro Y hY
        rw [Finset.mem_insert] at hY
        rcases hY with h | h
        · rw [h]
          refine le_trans (Finset.card_le_card ?_) (by rw [Finset.card_singleton]; omega)
          intro z hz
          rw [Finset.mem_sdiff] at hz
          by_cases hzp : z = p
          · rw [Finset.mem_singleton]
            exact hzp
          · exact False.elim (hz.2 (Finset.mem_union_right (s := U) (t := X.erase p)
              ((Finset.mem_erase (s := X) (b := p)).2 ⟨hzp, hz.1⟩)))
        · refine le_trans (Finset.card_le_card ?_) (hinv Y h)
          intro z hz
          rw [Finset.mem_sdiff] at hz
          exact Finset.mem_sdiff.mpr ⟨hz.1, fun hzU => hz.2 (Finset.mem_union_left _ hzU)⟩

/-- **THE DELETION SET OF A TWO-ATTACHMENT COVER.**

Let `𝒞` be a two-attachment cover of `G`.  There is a set `U` of at most `∑ X ∈ 𝒞, (|X| - 1)`
vertices such that **`𝒞` keeps at most one vertex of each of its members**, i.e.
`|X \ U| ≤ 1` for every `X ∈ 𝒞`.

This is `exists_oneSidedDeletion` — a statement about *arbitrary* families of nonempty vertex sets,
which needs no cycle at all — applied to the cover; it is the whole counting content of
`closeToBipartite_of_twoAttachCover'` below, isolated. -/
theorem exists_twoAttachDeletion (hc : TwoAttachCover' G 𝒞) :
    ∃ U : Finset V, U.card ≤ ∑ X ∈ 𝒞, (X.card - 1) ∧ ∀ X ∈ 𝒞, (X \ U).card ≤ 1 :=
  exists_oneSidedDeletion hc.1

/-- **THE TWO-ATTACHMENT COVER, PICK-FREE.**  If every member of `𝒞` is nonempty and every odd cycle
of `G` meets some member in at least two vertices, then `G` is the union of a bipartite graph and at
most `∑ X ∈ 𝒞, (|X| - 1)` vertices.

This is `JSP90.closeToBipartite_of_twoAttachCover` without the choice function, and it is the same
transversal: delete the set `U` of `exists_twoAttachDeletion`, which meets every odd cycle (two of
its vertices lie in some `X ∈ 𝒞`, and at most one of them is deleted). -/
theorem closeToBipartite_of_twoAttachCover' [Fintype V] (hc : TwoAttachCover' G 𝒞) :
    CloseToBipartite (∑ X ∈ 𝒞, (X.card - 1)) G := by
  obtain ⟨U, hU, hinv⟩ := exists_twoAttachDeletion (G := G) hc
  refine ⟨U, hU, ?_⟩
  refine isBipartite_delete_of_hitsOddCycles ?_
  intro D hD
  obtain ⟨X, hX, h2⟩ := hc.2 D hD
  by_contra hcon
  have hnotU : ∀ z : V, ¬ (z ∈ D ∩ U) := by
    intro z hz
    rw [hcon] at hz
    exact absurd hz (by simp)
  have hle : (D ∩ X).card ≤ 1 := by
    refine (Finset.card_le_card ?_).trans (hinv X hX)
    intro z hz
    rw [Finset.mem_sdiff]
    exact ⟨(Finset.mem_inter.mp hz).2, fun hzU => hnotU _
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1, hzU⟩)⟩
  omega

/-- **THE COVER WITH A BOUNDED CONSTANT — THE ERDŐS–PÓSA SHAPE.**  If a two-attachment cover of `G`
has at most `q` members, each of at most `ℓ` vertices, then `G` is the union of a bipartite graph
and at most `ℓ * q` vertices.

This is the form in which the cover statement is an Erdős–Pósa theorem: the constant is
*linear in the size of the cover*, so it is enough to bound the number of members and their size in
terms of the packing number. -/
theorem closeToBipartite_of_twoAttachCover'_bounded [Fintype V] {ℓ q : ℕ}
    (hc : TwoAttachCover' G 𝒞) (hb : ∀ X ∈ 𝒞, X.card ≤ ℓ) (hq : 𝒞.card ≤ q) :
    CloseToBipartite (ℓ * q) G := by
  refine CloseToBipartite.mono (closeToBipartite_of_twoAttachCover' hc) ?_
  have h1 : (∑ X ∈ 𝒞, (X.card - 1)) ≤ ∑ _X ∈ 𝒞, (ℓ - 1) :=
    Finset.sum_le_sum fun X hX => Nat.sub_le_sub_right (hb X hX) 1
  calc (∑ X ∈ 𝒞, (X.card - 1)) ≤ ∑ _X ∈ 𝒞, (ℓ - 1) := h1
    _ = (ℓ - 1) * 𝒞.card := by simp [Nat.mul_comm]
    _ ≤ ℓ * 𝒞.card := Nat.mul_le_mul_right 𝒞.card (Nat.sub_le ℓ 1)
    _ ≤ ℓ * q := Nat.mul_le_mul_left ℓ hq

/-- **ANOTHER INSTANCE OF THE HEADLINE THEOREM: THE PICK-FREE TWO-ATTACHMENT COVER CLASS.**
`LocIndep k G` together with a two-attachment cover `𝒞` gives `CloseToBipartite (∑ |X| - 1) G`, a
constant **independent of `k`**. -/
theorem erdos73On_of_twoAttachCover' [Fintype V] (k : ℕ) (hc : TwoAttachCover' G 𝒞)
    (_hG : LocIndep k G) : CloseToBipartite (∑ X ∈ 𝒞, (X.card - 1)) G :=
  closeToBipartite_of_twoAttachCover' hc

end Cover'

/-! ### Part 2 — **the machine-checked global target** -/

section Target

universe u

/-- **THE TWO-ATTACHMENT COVER EXISTS — THE MACHINE-CHECKED GLOBAL TARGET OF JSP-000090.**

Every finite graph whose odd cycle packings all have at most `r` members carries a two-attachment
cover with at most `q` members, each of them of at most `ℓ` vertices.

This is exactly the statement named as the residual blocker of round 112, and it is a `def`: it is
**not** assumed and **not** proved here.  It is the shape in which the classical Erdős–Pósa theorem
for odd cycles would have to be delivered to this development, because
`oddCycleErdosPosa_of_twoAttachCoverExists` below turns it into `OddCycleErdosPosa r` with the
explicit constant `ℓ * q`, and `erdos73_of_twoAttachCoverExists` turns *that* into Erdős Problem #73
itself.

The quantifier `q` on the number of members is what makes this an Erdős–Pósa statement rather than a
statement about one odd cycle: it is the analogue of `LocIndep.oddCycleFamily_card_le`, which bounds
the *number* of pairwise disjoint odd cycles. -/
def TwoAttachCoverExists (r ℓ q : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    (∀ 𝒞, IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) →
    ∃ 𝒞 : Finset (Finset W), TwoAttachCover' G 𝒞 ∧ 𝒞.card ≤ q ∧ ∀ X ∈ 𝒞, X.card ≤ ℓ

/-- **THE COVER STATEMENT IMPLIES ERDŐS–PÓSA FOR ODD CYCLES**, with the explicit constant `ℓ * q`:
`OddCycleErdosPosa r` is the assertion that a graph with no `r + 1` disjoint odd cycles is
`m`-close to bipartite for some `m`, and `m = ℓ * q` works here. -/
theorem oddCycleErdosPosa_of_twoAttachCoverExists {r ℓ q : ℕ}
    (h : TwoAttachCoverExists.{u} r ℓ q) : OddCycleErdosPosa.{u} r := by
  refine ⟨ℓ * q, fun W instW G hpack => ?_⟩
  obtain ⟨𝒞, hc, hcard, hlen⟩ := h W instW G hpack
  exact closeToBipartite_of_twoAttachCover'_bounded (G := G) hc hlen hcard

/-- **THE WHOLE OF ERDŐS PROBLEM #73 FOLLOWS FROM THE COVER STATEMENT.**

`∀ ℓ q, ∀ r, TwoAttachCoverExists r ℓ q` implies `∀ k, Erdős73 k` — i.e. `jsp_000090_main` — so the
single missing lemma of this development is now a single statement of the shape above, with no
hypothesis on `LocIndep`, no bound on the odd girth, no connectivity and no decomposition input. -/
theorem erdos73_of_twoAttachCoverExists {ℓ q : ℕ} (h : ∀ r, TwoAttachCoverExists.{u} r ℓ q) :
    ∀ k, Erdős73.{u} k := by
  intro k
  obtain ⟨m, hm⟩ := oddCycleErdosPosa_of_twoAttachCoverExists (h k)
  exact ⟨m, fun W instW G hG => hm W instW G fun C hC => hG.oddCycleFamily_card_le hC⟩

end Target

/-! ### Part 3 — the cover theorem, factored; and the **loss of a cycle cover** -/

section Packing

variable {𝒞 : Finset (Finset V)}

/-- **A TWO-ATTACHMENT PACKING**: a family of pairwise vertex-disjoint odd cycles such that **every
odd cycle of `G` meets one of its members in at least two vertices**.

A two-attachment packing is a cover whose members happen to be cycles, so it would give a
transversal through Part 1 — but, as Part 3 shows on the sharp witness `kTriangles k`, it gives one
of size `2 * k` where `k` is enough. -/
def TwoAttachPacking (G : SimpleGraph V) (𝒞 : Finset (Finset V)) : Prop :=
  IsOddCycleFamily (G := G) 𝒞 ∧
    (∀ D : Finset V, IsOddCycle G D → ∃ X ∈ 𝒞, 2 ≤ (D ∩ X).card)

/-- Every member of a two-attachment packing is nonempty (it is an odd cycle of length at least
`3`), so it is a cover. -/
theorem TwoAttachPacking.to_cover' (hc : TwoAttachPacking G 𝒞) : TwoAttachCover' G 𝒞 := by
  refine ⟨?_, hc.2⟩
  intro X hX
  have h3 : 3 ≤ X.card := isOddCycle_card_ge_three (hc.1.2 X hX)
  have hpos : 0 < X.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, ha⟩

/-- **A TWO-ATTACHMENT PACKING IS A COVER**, so it yields the transversal of Part 1. -/
theorem closeToBipartite_of_twoAttachPacking [Fintype V] (hc : TwoAttachPacking G 𝒞) :
    CloseToBipartite (∑ X ∈ 𝒞, (X.card - 1)) G :=
  closeToBipartite_of_twoAttachCover' (G := G) (hc.to_cover' (G := G))

/-- **TWO FIBRES OF `kTriangles k` ARE NEVER THE SAME SET.** -/
theorem ne_tri_of_ne {k : ℕ} {i j : Fin k} (hij : i ≠ j) : tri i ≠ tri j := by
  intro hcon
  have hmem : ((⟨0, by decide⟩ : Fin 3), i) ∈ tri j :=
    hcon ▸ (mem_tri (i := i)).2 rfl
  exact hij ((mem_tri (i := j)).mp hmem)

/-- **THE FIBRES OF `kTriangles k` ARE DISTINCT**, i.e. `tri i = tri j` forces `i = j`. -/
theorem eq_tri_of_eq {k : ℕ} {i j : Fin k} (hcon : tri i = tri j) : i = j := by
  have hmem : ((⟨0, by decide⟩ : Fin 3), i) ∈ tri j :=
    hcon ▸ (mem_tri (i := i)).2 rfl
  exact (mem_tri (i := j)).mp hmem

/-- **EQUAL INDICES GIVE EQUAL FIBRES.** -/
theorem tri_of_eq {k : ℕ} {i j : Fin k} (hij : i = j) : tri i = tri j := hij ▸ rfl

/-- **THE `Fin k` INDEX OF THE FIBRE IS DETERMINED BY THE FIBRE.** -/
theorem ne_of_ne_tri {k : ℕ} {i j : Fin k} (hne : tri i ≠ tri j) : i ≠ j :=
  fun hij => hne (tri_of_eq hij)

/-- **THE UNIVERSE OF A `Finset` IS THE UNIVERSE OF ITS `Set`.** -/
theorem univ_eq_univSet (k : ℕ) : ((Finset.univ : Finset (Fin k)) : Set (Fin k)) = Set.univ :=
  Set.ext fun _ => ⟨fun _ => trivial, fun _ => Finset.mem_univ _⟩

/-- **THE FIBRES OF `kTriangles k` ARE INJECTIVE**, as a function of the index. -/
theorem injOn_tri (k : ℕ) : Set.InjOn tri (((Finset.univ : Finset (Fin k)) : Set (Fin k))) := by
  intro i _ j _ h
  exact eq_tri_of_eq (i := i) (j := j) h

/-- **THE TRIANGLES THEMSELVES ARE A TWO-ATTACHMENT PACKING OF `kTriangles k`**: they are pairwise
disjoint odd cycles (`JSP90.disjointFamily_oddCycles_kTriangles`), and every odd cycle of
`kTriangles k` is one of them (`JSP90.exists_eq_tri_of_isOddCycle_kTriangles`), hence meets a member
in **three** vertices. -/
theorem twoAttachPacking_triangles (k : ℕ) :
    TwoAttachPacking (kTriangles k) ((Finset.univ : Finset (Fin k)).image tri) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro X hX Y hY hXY
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hY
    have hij : i ≠ j := ne_of_ne_tri hXY
    exact Finset.disjoint_iff_inter_eq_empty.mp (tri_disjoint hij)
  · intro X hX
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hX
    exact isOddCycle_tri i
  · intro D hD
    obtain ⟨i, rfl⟩ := exists_eq_tri_of_isOddCycle_kTriangles hD
    refine ⟨tri i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    have hself : tri i ∩ tri i = tri i := by
      apply Finset.Subset.antisymm
      · exact Finset.inter_subset_left
      · exact fun p hp => (Finset.mem_inter (s₁ := tri i) (s₂ := tri i)).2 ⟨hp, hp⟩
    rw [hself, card_tri]
    omega

/-- **THE COST OF THE CYCLE COVER OF `kTriangles k` IS `2 * k`.** -/
theorem sum_card_sub_one_tri (k : ℕ) :
    (∑ X ∈ (Finset.univ : Finset (Fin k)).image tri, (X.card - 1)) = 2 * k := by
  rw [Finset.sum_image (injOn_tri k)]
  simp [card_tri, Nat.mul_comm]

end Packing

/-! ### Part 4 — the cover is **exactly optimal** on the sharp witness, and cycles lose a factor 2 -/

section Sharp

/-- **THE DELETION SET OF A COVER MEETS EVERY ODD CYCLE.**  This is the transversal step of
`closeToBipartite_of_twoAttachCover'`, isolated. -/
theorem hitsOddCycles_of_twoAttachCover' [Fintype V] {U : Finset V} (hc : TwoAttachCover' G 𝒞)
    (_hU : U.card ≤ ∑ X ∈ 𝒞, (X.card - 1)) (hinv : ∀ X ∈ 𝒞, (X \ U).card ≤ 1) :
    HitsOddCycles G U := by
  intro D hD
  obtain ⟨X, hX, h2⟩ := hc.2 D hD
  by_contra hcon
  have hnotU : ∀ z : V, ¬ (z ∈ D ∩ U) := by
    intro z hz
    rw [hcon] at hz
    exact absurd hz (by simp)
  have hle : (D ∩ X).card ≤ 1 := by
    refine (Finset.card_le_card ?_).trans (hinv X hX)
    intro z hz
    rw [Finset.mem_sdiff]
    exact ⟨(Finset.mem_inter.mp hz).2, fun hzU => hnotU _
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1, hzU⟩)⟩
  omega

/-- **NO COVER OF `kTriangles k` COSTS LESS THAN `k`.**  A two-attachment cover has a deletion set of
size at most its cost which meets *every* odd cycle, hence meets the `k` pairwise disjoint triangles,
so the cost is at least `k` (`JSP90.card_le_of_hitsOddCycles_kTriangles`). -/
theorem cover_cost_ge_of_kTriangles {k : ℕ} {𝒞 : Finset (Finset (Fin 3 × Fin k))}
    (hc : TwoAttachCover' (kTriangles k) 𝒞) : k ≤ ∑ X ∈ 𝒞, (X.card - 1) := by
  obtain ⟨U, hU, hinv⟩ := exists_oneSidedDeletion hc.1
  exact le_trans (card_le_of_hitsOddCycles_kTriangles
    (hitsOddCycles_of_twoAttachCover' hc hU hinv)) hU

/-- **TWO VERTICES OF THE `i`-TH TRIANGLE** — the smallest possible member of a two-attachment cover
of `kTriangles k`, since a member has to meet a triangle in **two** vertices. -/
def triPair {k : ℕ} (i : Fin k) : Finset (Fin 3 × Fin k) :=
  {(⟨0, by decide⟩, i), (⟨1, by decide⟩, i)}

/-- **THE TWO-VERTEX COVER OF `kTriangles k`**: one pair per triangle. -/
def triPairCover (k : ℕ) : Finset (Finset (Fin 3 × Fin k)) :=
  (Finset.univ : Finset (Fin k)).image triPair

theorem mem_triPairCover {k : ℕ} {X : Finset (Fin 3 × Fin k)} :
    X ∈ triPairCover k ↔ ∃ i : Fin k, triPair i = X := by
  rw [triPairCover, Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_univ i, rfl⟩

theorem card_triPair {k : ℕ} (i : Fin k) : (triPair i).card = 2 := by
  simp [triPair]

theorem subset_triPair_tri {k : ℕ} (i : Fin k) : triPair i ⊆ tri i := by
  intro p hp
  simp only [triPair, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h
  · subst h
    exact (mem_tri (i := i)).2 rfl
  · subst h
    exact (mem_tri (i := i)).2 rfl

theorem card_inter_triPair {k : ℕ} (i : Fin k) : (tri i ∩ triPair i).card = 2 := by
  rw [Finset.Subset.antisymm Finset.inter_subset_right (fun p hp =>
    (Finset.mem_inter (s₁ := tri i) (s₂ := triPair i)).mpr ⟨subset_triPair_tri i hp, hp⟩)]
  exact card_triPair i

/-- **THE TWO-VERTEX COVER OF `kTriangles k` IS A TWO-ATTACHMENT COVER.**  Every odd cycle of
`kTriangles k` is a triangle `tri i`, and `triPair i ⊆ tri i` has two vertices, so every odd cycle
meets a member of the cover in **two** vertices. -/
theorem twoAttachCover'_triPairs (k : ℕ) : TwoAttachCover' (kTriangles k) (triPairCover k) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    obtain ⟨i, hX⟩ := (mem_triPairCover (k := k)).mp hX
    have hpos : 0 < (triPair i).card := by rw [card_triPair]; omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact ⟨a, by rw [← hX]; exact ha⟩
  · intro D hD
    obtain ⟨i, rfl⟩ := exists_eq_tri_of_isOddCycle_kTriangles hD
    refine ⟨triPair i, (mem_triPairCover (k := k)).mpr ⟨i, rfl⟩, ?_⟩
    have hself : tri i ∩ triPair i = triPair i := by
      apply Finset.Subset.antisymm
      · exact Finset.inter_subset_right
      · exact fun p hp =>
          (Finset.mem_inter (s₁ := tri i) (s₂ := triPair i)).mpr ⟨subset_triPair_tri i hp, hp⟩
    rw [hself, card_triPair]

/-- **THE PAIRS `triPair i` ARE INJECTIVE**, as a function of the index. -/
theorem injOn_triPair (k : ℕ) : Set.InjOn triPair (((Finset.univ : Finset (Fin k)) : Set (Fin k))) := by
  intro i _ j _ h
  have hm : ((⟨0, by decide⟩ : Fin 3), i) ∈ triPair i := by
    simp [triPair]
  have hm2 : ((⟨0, by decide⟩ : Fin 3), i) ∈ triPair j := h ▸ hm
  simp only [triPair, Finset.mem_insert, Finset.mem_singleton] at hm2
  rcases hm2 with heq | heq
  · exact (Prod.ext_iff.mp heq).2
  · exact ((Prod.ext_iff.mp heq.symm).2).symm

theorem sum_card_sub_one_triPairs (k : ℕ) :
    (∑ X ∈ triPairCover k, (X.card - 1)) = k := by
  rw [triPairCover, Finset.sum_image (injOn_triPair k)]
  simp [card_triPair]

/-- **THE MINIMUM COST OF A TWO-ATTACHMENT COVER OF `kTriangles k` IS EXACTLY `k`** — which is also
the odd cycle transversal number of `kTriangles k` (`JSP90.closeToBipartite_iff`).  So the cover
route of Part 1 is **optimal in constant** on the family that makes Erdős #73 hard: all that Part 2's
`TwoAttachCoverExists` has to deliver is a cover with `q` members of size `ℓ` depending on the
packing number. -/
theorem cover_cost_min_kTriangles (k : ℕ) :
    (∀ 𝒞 : Finset (Finset (Fin 3 × Fin k)), TwoAttachCover' (kTriangles k) 𝒞 →
      k ≤ ∑ X ∈ 𝒞, (X.card - 1)) ∧ (∑ X ∈ triPairCover k, (X.card - 1)) = k :=
  ⟨fun _ hc => cover_cost_ge_of_kTriangles hc, sum_card_sub_one_triPairs k⟩

/-- **THE COVER BOUND IS EXACTLY OPTIMAL ON THE SHARP WITNESS.**  The two-attachment cover theorem
costs `k` on `kTriangles k` (`sum_card_sub_one_triPairs`), and `k` is the exact value of the
conclusion there (`JSP90.closeToBipartite_iff`: `CloseToBipartite m (kTriangles k) ↔ k ≤ m`), so no
constant below `k` works there. -/
theorem cover_cost_kTriangles_is_optimal (k : ℕ) :
    CloseToBipartite k (kTriangles k) ∧
      ∀ m : ℕ, m < k → ¬ CloseToBipartite m (kTriangles k) := by
  have hle : CloseToBipartite (∑ X ∈ triPairCover k, (X.card - 1)) (kTriangles k) :=
    closeToBipartite_of_twoAttachCover' (G := kTriangles k) (twoAttachCover'_triPairs k)
  rw [sum_card_sub_one_triPairs k] at hle
  refine ⟨hle, fun m hm hcon => ?_⟩
  have h := (closeToBipartite_iff (k := k) (m := m)).mp hcon
  omega

/-- **BUT A COVER WHOSE MEMBERS ARE CYCLES LOSES A FACTOR 2.**  The triangles are a two-attachment
*packing* of `kTriangles k` (`twoAttachPacking_triangles`), so they are a cover, and their cost is
`2 * k` (`sum_card_sub_one_tri`) — exactly **twice** the optimum `k` of
`cover_cost_kTriangles_is_optimal`, which is attained by `triPairCover`.

So the members of a two-attachment cover must be allowed to be **vertex sets that are not odd
cycles**: restricting them to cycles throws away exactly the factor two that the sharp witness
measures.  This is the concrete reason why `TwoAttachCover'` of Part 1 is stated for arbitrary
vertex sets. -/
theorem packing_cover_cost_two_of_kTriangles (k : ℕ) :
    CloseToBipartite (2 * k) (kTriangles k) ∧
      ∀ m : ℕ, m < k → ¬ CloseToBipartite m (kTriangles k) := by
  have hle : CloseToBipartite (∑ X ∈ (Finset.univ : Finset (Fin k)).image tri, (X.card - 1))
      (kTriangles k) :=
    closeToBipartite_of_twoAttachPacking (twoAttachPacking_triangles k)
  rw [sum_card_sub_one_tri] at hle
  refine ⟨hle, fun m hm hcon => ?_⟩
  have h := (closeToBipartite_iff (k := k) (m := m)).mp hcon
  omega

end Sharp

end

end JSP90