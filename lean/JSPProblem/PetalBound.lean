/-
# JSP-000090 — `JSPProblem/PetalBound.lean`: the ATTACHMENT SET IS NOT CHARGED AGAINST THE
#   DEFICIENCY — and a new instance of the headline theorem that is

`discovery/JSP-000090/policy.json` (round 119) left exactly one concrete blocker for
`jsp_000090_main`:

> the absorption step of `JSPProblem/Petal.lean` is now `q + a + (|C| - 1)` with
> `a = |PetalSet G C|`, so the single missing lemma is a purely *numerical* one: there is a function
> `phi(k)` with `|PetalSet G C| <= phi(k)` for every graph with `LocIndep k G` and every odd cycle `C`.

Round 119 did not have the concrete witnesses for that step.  This file supplies them, and answers
the blocker in two halves: **the naive numerical shape is false (machine-checked), and the correct
shape is a packing cover (proved), which yields a new instance of Erdős #73.**

## Part 1–2 — the charging lemmas, and a NEW INSTANCE of the headline theorem

The attachment set is a subset of `C`, and each vertex of it is the attachment point of a **petal**
(`JSP90.OneAttach`, an odd cycle meeting `C` in exactly one vertex).  Two attachment points covered
by a *packing* of petals must be covered by *different* members of that packing, so:

* **`JSP90.card_petalSet_inter_biUnion_le_card`** — the attachment points lying on a family `𝒟` of
  petals number at most `|𝒟|`;
* **`JSP90.card_petalSet_inter_biUnion_le_maxDef`** — and at most `MaxDef G`, because a packing of
  petals is a packing of odd cycles and `JSP90.card_le_of_maxDef_le` charges a packing of odd cycles
  against the deficiency (`LocIndep k G` ↔ `MaxDef G ≤ k`);
* **`JSP90.card_petalSet_le_maxDef_of_cover`** — so **`|PetalSet G C| ≤ MaxDef G`** holds whenever the
  attachment set is covered by a packing of petals;
* **`JSP90.card_petalSet_le_maxDef_add`** — the general form: the attachment set is charged against
  the deficiency **up to** the attachment points the packing misses;
* **`JSP90.exists_petal_hits_biUnion_offC`** — **what a maximal petal packing does NOT pay for**:
  every attachment point outside the packing carries a petal that meets the packing **off `C`**.  This
  localises the residue of the classical Mader step to a single statement;
* **`JSP90.closeToBipartite_of_petalSet_le_maxDef`** is the bridge: any bound on the attachment set
  in terms of `MaxDef G` turns into Erdős's conclusion;
* **`JSP90.closeToBipartite_of_petalPackingCover` / `JSP90.erdos73On_of_petalPackingCover` — A NEW
  INSTANCE OF THE HEADLINE THEOREM, WITH THE CONSTANT `k + |C| - 1`** — and its triangle level
  **`JSP90.closeToBipartite_of_petalPackingCover_triangle`, constant `k + 2`** (Erdős's hypothesis, an
  odd cycle `C` meeting every odd cycle of `G`, and a packing of petals covering the attachment set).
  `JSP90.OneCyclePetal G ℓ` is the class-level statement, a `def` and *not* assumed, with the
  reduction `JSP90.erdos73On_of_oneCyclePetal`; both are realised on the concrete graph of Part 4
  (`JSP90.erdos73On_propeller`, `JSP90.oneCyclePetal_prop`).

## Part 3–4 — the nine-vertex propeller: the `|C| - 1` term is NOT enough once petals exist

`prop` (`JSPProblem/PetalFinite.lean`) is the triangle `0 - 1 - 2 - 0` with a pendant triangle at each
of its vertices; `C = {0, 1, 2}` and the three pendant triangles are petals of `C`:

* `maxDef_prop : MaxDef prop = 3`, `petalSet_propC : PetalSet prop propC = propC`,
  `isBipartite_delete_propC` — so **every odd cycle of `prop` meets `C`**;
* `closeToBipartite_three_prop` and **`not_closeToBipartite_two_prop`**: the odd cycle transversal
  number of the propeller is exactly `3 = |C|`.  Hence **`not_closeToBipartite_two_prop_of_cardC`**
  refutes `CloseToBipartite (|C| - 1) G` on a graph whose attachment set is non-empty: the
  two-attachment / `petalSet_empty` bound of `JSPProblem/Petal.lean` genuinely needs its hypothesis,
  and the attachment points of `C` are exactly what must be paid for.  This is the nine-vertex
  witness promised by round 119;
* the three pendant triangles **are** a packing of petals covering the attachment set
  (`isOddCycleFamily_propPetals`, `prop_petalPackingCover`), so the new instance applies to `prop`.

## Part 5 — the seven-vertex `g7`: the attachment set is LARGER than the deficiency

`g7` is `K_4` on `{0, 1, 2, 3}` with an independent set `{4, 5, 6}`, where `4 ~ {0, 3}`, `5 ~ {1, 3}`,
`6 ~ {2, 3}`; with `C = {0, 1, 2}` the triangles `{0, 3, 4}`, `{1, 3, 5}`, `{2, 3, 6}` are petals:

* `maxDef_g7 : MaxDef g7 = 2`, `petalSet_g7C : PetalSet g7 g7C = g7C`, so
  `card_petalSet_g7C : |PetalSet g7 g7C| = 3`;
* **`JSP90.not_petalSet_le_maxDef_g7 : ¬ (|PetalSet g7 g7C| ≤ MaxDef g7)`** — a machine-checked
  refutation of the first guess at the round-119 bound (`|PetalSet G C| ≤ MaxDef G`).  Any `phi` with
  `|PetalSet G C| ≤ phi (MaxDef G)` must have `phi 2 ≥ 3`, so `phi` is **not** `MaxDef` and **not**
  `MaxDef / 2`.  The next guess, `|PetalSet| ≤ 2 * MaxDef`, survives this witness (`3 ≤ 4`) and is
  *false as a refutation* — the kernel rejects it (round 120, `policy.json`: `2 * MaxDef` cannot be
  refuted on `g7`, so a factor of `3 / 2` is all this witness forces);
* `not_inter_empty_g7T0_g7T1` and `not_oddCycleFamily_g7Petals`: the three petals all contain the
  vertex `3`, so they are **not** a packing — the packing-cover hypothesis of
  `JSP90.card_petalSet_le_maxDef_of_cover` is real content, and it is exactly what `g7` fails.

## What is *not* proved

`PetalSet G C ⊆ ⋃ 𝒟` for a packing of petals (`JSP90.OneCyclePetal`) is **not** available in general:
`JSP90.card_petalSet_le_maxDef_add` and `JSP90.exists_petal_hits_biUnion_offC` say exactly what is
missing — the attachment points whose petals all pass through a point of the packing outside `C`.
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and `jsp_000090_main` are unchanged.

## Toolchain notes for the next round (round 120)

* `local instance` is **not** scoped to its `section`, and a later re-declaration does **not** shadow
  a more specific instance.  `JSPProblem/PetalFinite.lean` needs the *computable*
  `instDecidableEqFin n` (for `decide`) while this file needs the *classical* instance (to match
  `JSP90.IsOddCycle`, `JSP90.OneAttach` and `JSP90.mem_petalSet`, whose statements were elaborated in
  `JSPProblem/Transversal.lean` with `Classical.decEq`): the two scopes must live in **two files**;
* with a classical `DecidableEq (Fin n)` **no** finset literal reduces: `Finset.insert` is defined by a
  case analysis on the instance, so `#({0, 1, 2} : Finset (Fin 9))` does not compute and `decide`
  fails on `= 3` (`JSP90.card_triple` replaces it).  Worse, **`simp` and `decide` on `Fin` literals
  produce an ill-typed `eq_false_of_decide` term and the kernel rejects it**, so *every* statement
  about a concrete witness here is proved with `JSP90.fin_mem_triple`, `JSP90.not_mem_triple`,
  `JSP90.fin3_not_mem`, `JSP90.fin_ne_val` and `simp only [Finset.mem_insert, Finset.mem_singleton]`
  (which rewrites a triple membership into a three-fold disjunction without any computation);
* `simp only [Finset.mem_sdiff, …] at h` is a no-op here: `JSP90.deleteFinset_adj` has already
  produced `u ∉ X`;
* `IsBipartite` at this revision is `∃ d, ∀ u v, Adj u v → d u ≠ d v` with `d : V → Fin 2`, so
  `intro he` yields a **`Fin 2`** equality; use `Fin.mk.inj he` to get the `Nat` one;
* `g7Adj`/`propAdj` are `def`s, not `Iff`s: `rw [g7_adj] at hadj` before `rcases`;
* `section Prop` is a syntax error (`Prop` is a type); `DisjointFamily` is `JSP90`'s own predicate
  (`∀ X ∈ C, ∀ Y ∈ C, X ≠ Y → X ∩ Y = ∅`); `Finset.mem_insert_of_mem` has the shape
  `(a) (b) (s) (h : a ∈ s)`.
-/

import JSPProblem.Petal
import JSPProblem.PetalFinite
import JSPProblem.Additive

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance petalBoundDecidableEq : DecidableEq V := Classical.decEq V

/-- ... and the same instance on `Fin n`, which is what `JSPProblem/Petal.lean` and
`JSPProblem/Transversal.lean` use to elaborate `OneAttach`, `PetalSet` and `IsOddCycle`; without it a
statement about `Finset (Fin 7)` here would silently use Mathlib's computable `instDecidableEqFin` and
stop matching them. -/
local instance petalBoundEqFin (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-! ### Part 0 — small helpers: a classical `DecidableEq` forbids `decide` and `simp` on `Fin` -/

section Helpers

/-- Two `Fin n` of different values are different: the `decide`-free replacement for
`(a : Fin n) ≠ b`. -/
theorem fin_ne_val {n a b : ℕ} (ha : a < n) (hb : b < n) (h : a ≠ b) :
    (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := by
  intro he
  exact h (Fin.mk.inj he)

/-- Two `Fin n` with the same value are equal. -/
theorem fin_eq_of_val_eq {x y : Fin n} (h : x.val = y.val) : x = y := Fin.ext h

/-- **MEMBERSHIP IN A TRIPLE IS A THREE-FOLD DISJUNCTION.**  No computation is involved. -/
theorem fin_mem_triple {n a b c x : Fin n} (h : x ∈ ({a, b, c} : Finset (Fin n))) :
    x = a ∨ x = b ∨ x = c := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

/-- ... and, for a triple of pairwise distinct `Fin n`, membership in each of the three positions. -/
theorem mem_first_triple {V} [DecidableEq V] (a b c : V) : a ∈ ({a, b, c} : Finset V) :=
  Finset.mem_insert_self a _

theorem mem_mid_triple {V} [DecidableEq V] (a b c : V) : b ∈ ({a, b, c} : Finset V) :=
  Finset.mem_insert_of_mem (a := b) (b := a) (Finset.mem_insert_self b _)

theorem mem_last_triple {V} [DecidableEq V] (a b c : V) : c ∈ ({a, b, c} : Finset V) :=
  Finset.mem_insert_of_mem (a := c) (b := a)
    (Finset.mem_insert_of_mem (a := c) (b := b) (Finset.mem_singleton_self c))



/-- **TWO VERTEX SETS MEET IN ONE POINT.**  If every common point of `s` and `t` is `a`, and `a` lies in
both, then `s ∩ t = {a}`.  This is the counting input behind "`D ∩ C = {v}`" for a concrete petal. -/
theorem inter_eq_singleton {s t : Finset V} {a : V}
    (h : ∀ x : V, x ∈ s → x ∈ t → x = a) (ha : a ∈ s) (ha' : a ∈ t) : s ∩ t = {a} := by
  refine Finset.Subset.antisymm
    (fun x hx =>
      Finset.mem_singleton.mpr (h x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2)) ?_
  intro x hx
  have hxa : x = a := Finset.mem_singleton.mp hx
  exact Finset.mem_inter.mpr ⟨by rw [hxa]; exact ha, by rw [hxa]; exact ha'⟩

/-- **TWO `Fin` TRIPLES MEET IN THE POINT `p`.**  The generic form used by every concrete petal below:
if the two triples have no common point but `p`, they meet exactly in `p`. -/
theorem fin_inter_tri_tri {n a b c d e f p : Fin n}
    (hne : ∀ x : Fin n, (x = a ∨ x = b ∨ x = c) → (x = d ∨ x = e ∨ x = f) → x = p)
    (hp : p = a ∨ p = b ∨ p = c) (hp' : p = d ∨ p = e ∨ p = f) :
    ({a, b, c} : Finset (Fin n)) ∩ ({d, e, f} : Finset (Fin n)) = {p} := by
  refine inter_eq_singleton (s := {a, b, c}) (t := {d, e, f}) (a := p) ?_ ?_ ?_
  · intro x hx1 hx2
    exact hne x (fin_mem_triple hx1) (fin_mem_triple hx2)
  · rcases hp with hp | hp | hp
    · have hpa : p = a := fin_eq_of_val_eq (Fin.ext_iff.mp hp)
      rw [hpa]; exact mem_first_triple a b c
    · have hpb : p = b := fin_eq_of_val_eq (Fin.ext_iff.mp hp)
      rw [hpb]; exact mem_mid_triple a b c
    · have hpc : p = c := fin_eq_of_val_eq (Fin.ext_iff.mp hp)
      rw [hpc]; exact mem_last_triple a b c
  · rcases hp' with hp' | hp' | hp'
    · have hpd : p = d := fin_eq_of_val_eq (Fin.ext_iff.mp hp')
      rw [hpd]; exact mem_first_triple d e f
    · have hpe : p = e := fin_eq_of_val_eq (Fin.ext_iff.mp hp')
      rw [hpe]; exact mem_mid_triple d e f
    · have hpf : p = f := fin_eq_of_val_eq (Fin.ext_iff.mp hp')
      rw [hpf]; exact mem_last_triple d e f

/-- ... and two `Fin` triples with no common point are disjoint. -/
theorem fin_inter_tri_tri_empty {n a b c d e f : Fin n}
    (hne : ∀ x : Fin n, (x = a ∨ x = b ∨ x = c) → (x = d ∨ x = e ∨ x = f) → False) :
    ({a, b, c} : Finset (Fin n)) ∩ ({d, e, f} : Finset (Fin n)) = ∅ := by
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  exact hne x (fin_mem_triple (Finset.mem_inter.mp hx).1)
    (fin_mem_triple (Finset.mem_inter.mp hx).2)

/-- **THE CARDINALITY OF A TRIPLE OF PAIRWISE DISTINCT ELEMENTS**, by hand: with a classical
`DecidableEq` the finset literal `{a, b, c}` does not reduce, so this replaces `by decide`. -/
theorem card_triple {V} [DecidableEq V] {a b c : V} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  have hab : a ∉ ({b, c} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  have hbc : b ∉ ({c} : Finset V) := by
    simp only [Finset.mem_singleton]
    exact h3
  rw [Finset.card_insert_of_notMem hab, Finset.card_insert_of_notMem hbc, Finset.card_singleton]

end Helpers

/-! ### Part 1 — the attachment set is charged against the deficiency -/

section Charge

/-- A family of pairwise vertex-disjoint petals is a family of pairwise vertex-disjoint odd cycles. -/
theorem isOddCycleFamily_of_oneAttach {C : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hdisj : DisjointFamily 𝒟) :
    IsOddCycleFamily (G := G) 𝒟 :=
  ⟨hdisj, fun D hD => (h𝒟 D hD).1⟩

/-- **THE ATTACHMENT POINTS ON A FAMILY OF PETALS ARE COUNTED BY THE FAMILY.**  Two vertices of
`PetalSet G C` lying on the same petal would both be attachment points of it, but a petal has a
*single* attachment point; so at most `|𝒟|` vertices of `C` lie on `⋃ 𝒟`. -/
theorem card_petalSet_inter_biUnion_le_card {C : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) :
    (PetalSet G C ∩ 𝒟.biUnion id).card ≤ 𝒟.card := by
  have hsub : PetalSet G C ∩ 𝒟.biUnion id ⊆ 𝒟.biUnion (fun D => D ∩ C) := by
    intro v hv
    obtain ⟨hvP, hvU⟩ := Finset.mem_inter.mp hv
    obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hvU
    exact Finset.mem_biUnion.mpr
      ⟨D, hD, Finset.mem_inter.mpr ⟨hvD, petalSet_subset (C := C) hvP⟩⟩
  calc (PetalSet G C ∩ 𝒟.biUnion id).card ≤ (𝒟.biUnion (fun D => D ∩ C)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ D ∈ 𝒟, (D ∩ C).card := Finset.card_biUnion_le
    _ = ∑ _D ∈ 𝒟, (1 : ℕ) := Finset.sum_congr rfl fun D hD => (h𝒟 D hD).2
    _ = 𝒟.card := by simp

/-- **THE ATTACHMENT SET IS CHARGED AGAINST THE DEFICIENCY.**  The attachment points lying on a
*packing* of petals number at most `MaxDef G`, since each member of the packing is an odd cycle and
`JSP90.card_le_of_maxDef_le` charges a packing of odd cycles against the deficiency. -/
theorem card_petalSet_inter_biUnion_le_maxDef {C : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟) :
    (PetalSet G C ∩ 𝒟.biUnion id).card ≤ MaxDef G :=
  (card_petalSet_inter_biUnion_le_card h𝒟).trans
    (card_le_of_maxDef_le (r := MaxDef G) (Nat.le_refl _) hfam)

/-- **`|PetalSet G C| ≤ MaxDef G` UNDER A PACKING COVER.**  This is the shape of the numerical
blocker of round 119, with one extra hypothesis: the attachment set is covered by a packing of
petals. -/
theorem card_petalSet_le_maxDef_of_cover {C : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hcover : PetalSet G C ⊆ 𝒟.biUnion id) : (PetalSet G C).card ≤ MaxDef G := by
  have h1 : (PetalSet G C \ 𝒟.biUnion id).card = 0 :=
    Finset.card_eq_zero.mpr ((sdiff_eq_empty_iff_subset).mpr hcover)
  have h2 := Finset.card_sdiff_add_card_inter (PetalSet G C) (𝒟.biUnion id)
  have h3 := card_petalSet_inter_biUnion_le_maxDef h𝒟 hfam
  omega

/-- **THE UNCHARGED RESIDUE.**  The attachment set is charged against `MaxDef G` up to the attachment
points which no member of `𝒟` reaches. -/
theorem card_petalSet_le_maxDef_add {C : Finset V} {𝒟 : Finset (Finset V)}
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟) :
    (PetalSet G C).card ≤ MaxDef G + (PetalSet G C \ 𝒟.biUnion id).card := by
  have h1 := card_petalSet_inter_biUnion_le_maxDef h𝒟 hfam
  have h2 := Finset.card_sdiff_add_card_inter (PetalSet G C) (𝒟.biUnion id)
  omega

/-- **WHAT A MAXIMAL PETAL PACKING DOES NOT PAY FOR.**  Let `𝒟` be a packing of petals which is
*maximal* in the sense that every petal meets one of its members.  Then every attachment point `v` of
`C` outside `⋃ 𝒟` carries a petal that meets `⋃ 𝒟` **off `C`**: the intersection point cannot lie on
`C`, since a petal meets `C` only at its own attachment point, which would put `v` on `⋃ 𝒟`.

This is the local statement the classical Mader step would have to control; everything else in
`card_petalSet_le_maxDef_add` is paid for. -/
theorem exists_petal_hits_biUnion_offC {C : Finset V} {𝒟 : Finset (Finset V)}
    (_h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D)
    (hmax : ∀ D : Finset V, OneAttach G C D → ∃ D' ∈ 𝒟, D ∩ D' ≠ ∅) {v : V}
    (hv : v ∈ PetalSet G C \ 𝒟.biUnion id) :
    ∃ D : Finset V, IsOddCycle G D ∧ D ∩ C = {v} ∧ (D ∩ (𝒟.biUnion id \ C)).Nonempty := by
  obtain ⟨hvP, hvU⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨-, D, hD, hDinter⟩ := mem_petalSet.mp hvP
  have hcard : (D ∩ C).card = 1 := by rw [hDinter]; simp
  obtain ⟨D', hD', hmeet⟩ := hmax D ⟨hD, hcard⟩
  obtain ⟨z, hz⟩ := (Finset.nonempty_iff_ne_empty (s := D ∩ D')).mpr hmeet
  obtain ⟨hzD, hzD'⟩ := Finset.mem_inter.mp hz
  refine ⟨D, hD, hDinter, ⟨z, Finset.mem_inter.mpr ⟨hzD, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨D', hD', hzD'⟩
  · intro hzC
    have hzDv : z = v := by
      have hzDC : z ∈ D ∩ C := Finset.mem_inter.mpr ⟨hzD, hzC⟩
      rw [hDinter] at hzDC
      exact Finset.mem_singleton.mp hzDC
    exact hvU (by rw [hzDv.symm]; exact Finset.mem_biUnion.mpr ⟨D', hD', hzD'⟩)

/-- **`|PetalSet G C| ≤ MaxDef G` IS ENOUGH.**  The attachment set is the only parameter of
`JSP90.closeToBipartite_of_petalSet`, so *any* bound on it in terms of `MaxDef G` turns into Erdős's
conclusion: this is the bridge between the numerical blocker of round 119 and the headline theorem. -/
theorem closeToBipartite_of_petalSet_le_maxDef {C : Finset V} {k : ℕ} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ MaxDef G) (hG : LocIndep k G) :
    CloseToBipartite (k + (C.card - 1)) G := by
  have h := closeToBipartite_of_petalSet (C := C) (a := MaxDef G) hC hmeet ha
  refine closeToBipartite_mono ?_ h
  have hmd := maxDef_le_of_locIndep hG
  omega

theorem erdos73On_of_petalSet_le_maxDef {C : Finset V} {k : ℕ} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ MaxDef G) (hG : LocIndep k G) :
    CloseToBipartite (k + (C.card - 1)) G :=
  closeToBipartite_of_petalSet_le_maxDef hC hmeet ha hG

end Charge

/-! ### Part 2 — a new instance of the headline theorem -/

section Instance

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE CONSTANT `k + |C| - 1`.**  If `C` is an odd
cycle of `G` meeting every odd cycle of `G`, and the attachment set of `C` is covered by a packing of
petals, then `G` is the union of a bipartite graph and at most `k + |C| - 1` vertices. -/
theorem closeToBipartite_of_petalPackingCover {C : Finset V} {𝒟 : Finset (Finset V)} {k : ℕ}
    (hC : IsOddCycle G C) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hcover : PetalSet G C ⊆ 𝒟.biUnion id) (hG : LocIndep k G) :
    CloseToBipartite (k + (C.card - 1)) G :=
  closeToBipartite_of_petalSet_le_maxDef hC hmeet
    (card_petalSet_le_maxDef_of_cover h𝒟 hfam hcover) hG

/-- The headline-theorem form of `closeToBipartite_of_petalPackingCover`. -/
theorem erdos73On_of_petalPackingCover {C : Finset V} {𝒟 : Finset (Finset V)} {k : ℕ}
    (hC : IsOddCycle G C) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hcover : PetalSet G C ⊆ 𝒟.biUnion id) (hG : LocIndep k G) :
    CloseToBipartite (k + (C.card - 1)) G :=
  closeToBipartite_of_petalPackingCover hC hmeet h𝒟 hfam hcover hG

/-- **THE INSTANCE WITH AN EXPLICIT ODD-GIRTH PARAMETER**: the same conclusion
`CloseToBipartite (k + (ℓ - 1)) G` whenever `|C| ≤ ℓ`. -/
theorem closeToBipartite_of_petalPackingCover_of_card_le {C : Finset V} {𝒟 : Finset (Finset V)}
    {k ℓ : ℕ} (hC : IsOddCycle G C) (hℓ : C.card ≤ ℓ)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hcover : PetalSet G C ⊆ 𝒟.biUnion id) (hG : LocIndep k G) :
    CloseToBipartite (k + (ℓ - 1)) G := by
  have h3 := isOddCycle_card_ge_three hC
  have h := closeToBipartite_of_petalPackingCover hC hmeet h𝒟 hfam hcover hG
  refine closeToBipartite_mono ?_ h
  omega

/-- **THE TRIANGLE LEVEL: THE CONSTANT `k + 2`.**  A triangle `C` meeting every odd cycle of `G`, with
its attachment set covered by a packing of petals, gives `CloseToBipartite (k + 2) G`. -/
theorem closeToBipartite_of_petalPackingCover_triangle {C : Finset V} {𝒟 : Finset (Finset V)}
    {k : ℕ} (hC : IsOddCycle G C) (hC3 : C.card = 3)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hcover : PetalSet G C ⊆ 𝒟.biUnion id) (hG : LocIndep k G) :
    CloseToBipartite (k + 2) G := by
  have h := closeToBipartite_of_petalPackingCover hC hmeet h𝒟 hfam hcover hG
  simpa [hC3] using h

/-- The headline-theorem form of the triangle level. -/
theorem erdos73On_of_petalPackingCover_triangle {C : Finset V} {𝒟 : Finset (Finset V)} {k : ℕ}
    (hC : IsOddCycle G C) (hC3 : C.card = 3)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (h𝒟 : ∀ D ∈ 𝒟, OneAttach G C D) (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hcover : PetalSet G C ⊆ 𝒟.biUnion id) (hG : LocIndep k G) :
    CloseToBipartite (k + 2) G :=
  closeToBipartite_of_petalPackingCover_triangle hC hC3 hmeet h𝒟 hfam hcover hG

/-- **THE CLASS-LEVEL STATEMENT**, in the shape of `JSP90.TwoAttachCoverExists` of round 115: some odd
cycle `C` of at most `ℓ` vertices meets every odd cycle of `G`, and its attachment set is charged
against the deficiency.

This is a `def`, and it is **not** assumed anywhere. -/
def OneCyclePetal (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ C : Finset V, IsOddCycle G C ∧ C.card ≤ ℓ ∧
    (∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) ∧ (PetalSet G C).card ≤ MaxDef G

/-- **THE REDUCTION**: `OneCyclePetal G ℓ` gives Erdős's conclusion with the constant `k + (ℓ - 1)`. -/
theorem closeToBipartite_of_oneCyclePetal {k ℓ : ℕ} (hℓ : 3 ≤ ℓ) (h : OneCyclePetal G ℓ)
    (hG : LocIndep k G) : CloseToBipartite (k + (ℓ - 1)) G := by
  obtain ⟨C, hC, hCcard, hmeet, ha⟩ := h
  have h3 := isOddCycle_card_ge_three hC
  have hstep := closeToBipartite_of_petalSet_le_maxDef hC hmeet ha hG
  refine closeToBipartite_mono ?_ hstep
  omega

theorem erdos73On_of_oneCyclePetal {k ℓ : ℕ} (hℓ : 3 ≤ ℓ) (h : OneCyclePetal G ℓ)
    (hG : LocIndep k G) : CloseToBipartite (k + (ℓ - 1)) G :=
  closeToBipartite_of_oneCyclePetal hℓ h hG

end Instance

/-! ### Part 3 — a generic triangle, and a helper for literal intersections -/

section Triple

/-- **A PAIRWISE ADJACENT TRIPLE OF DISTINCT VERTICES IS AN ODD CYCLE.**  For `a b c` pairwise
adjacent and pairwise distinct, the finset `{a, b, c}` is an odd cycle, in the exact sense of
`JSP90.IsOddCycle`: a cyclic ordering of three adjacent vertices.  Every concrete witness of this file
is built from it. -/
theorem isOddCycle_triple {n : ℕ} (H : SimpleGraph (Fin n)) {a b c : Fin n} {t : Fin 3 → Fin n}
    (hinj : Function.Injective t)
    (hcyc : ∀ j : Fin 3, H.Adj (t j) (t (cycSucc j)))
    (ht0 : t 0 = a) (ht1 : t 1 = b) (ht2 : t 2 = c) : IsOddCycle H {a, b, c} := by
  refine ⟨3, t, by decide, by decide, hinj, hcyc, ?_⟩
  intro x
  constructor
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact ⟨0, ht0.trans hx.symm⟩
    · exact ⟨1, ht1.trans hx.symm⟩
    · exact ⟨2, ht2.trans hx.symm⟩
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [ht0, ht1, ht2]

end Triple

/-! ### Part 4 — the nine-vertex propeller: the `|C| - 1` term is NOT enough -/

section Propeller

/-- The central triangle `C = {0, 1, 2}` of `prop`. -/
def propC : Finset (Fin 9) := {0, 1, 2}

/-- The pendant triangle `{0, 3, 4}`. -/
def propT0 : Finset (Fin 9) := {0, 3, 4}

/-- The pendant triangle `{1, 5, 6}`. -/
def propT1 : Finset (Fin 9) := {1, 5, 6}

/-- The pendant triangle `{2, 7, 8}`. -/
def propT2 : Finset (Fin 9) := {2, 7, 8}

theorem propC_eq : propC = ({0, 1, 2} : Finset (Fin 9)) := rfl

theorem propT0_eq : propT0 = ({0, 3, 4} : Finset (Fin 9)) := rfl

theorem propT1_eq : propT1 = ({1, 5, 6} : Finset (Fin 9)) := rfl

theorem propT2_eq : propT2 = ({2, 7, 8} : Finset (Fin 9)) := rfl

theorem mem_propC_iff {x : Fin 9} : x ∈ propC ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  rw [propC_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- `C = {0, 1, 2}` is an odd cycle of `prop`. -/
theorem isOddCycle_propC : IsOddCycle prop propC := by
  refine isOddCycle_triple prop propCCyc_inj propCCyc_cyc rfl rfl rfl

theorem isOddCycle_propT0 : IsOddCycle prop propT0 := by
  refine isOddCycle_triple prop propT0Cyc_inj propT0Cyc_cyc rfl rfl rfl

theorem isOddCycle_propT1 : IsOddCycle prop propT1 := by
  refine isOddCycle_triple prop propT1Cyc_inj propT1Cyc_cyc rfl rfl rfl

theorem isOddCycle_propT2 : IsOddCycle prop propT2 := by
  refine isOddCycle_triple prop propT2Cyc_inj propT2Cyc_cyc rfl rfl rfl

/-- **THE RESIDUE OF `C` IS THE MATCHING `3 - 4`, `5 - 6`, `7 - 8`,** so it is bipartite and therefore
**every odd cycle of `prop` meets `C`** — the residue hypothesis of
`JSP90.closeToBipartite_of_petalSet`.  The parity is the only computation: two vertices of the residue
in the same pendant triangle differ by one, and two vertices of the residue in different pendant
triangles are never adjacent. -/
theorem isBipartite_delete_propC : (deleteFinset prop propC).IsBipartite := by
  refine ⟨fun v => ⟨(v.val + 1) % 2, Nat.mod_lt _ (by decide)⟩, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  rw [mem_propC_iff] at h1
  rw [mem_propC_iff] at h2
  have hu0 : u ≠ 0 := fun he => h1 (Or.inl he)
  have hu1 : u ≠ 1 := fun he => h1 (Or.inr (Or.inl he))
  have hu2 : u ≠ 2 := fun he => h1 (Or.inr (Or.inr he))
  have hv0 : v ≠ 0 := fun he => h2 (Or.inl he)
  have hv1 : v ≠ 1 := fun he => h2 (Or.inr (Or.inl he))
  have hv2 : v ≠ 2 := fun he => h2 (Or.inr (Or.inr he))
  have hu : 3 ≤ u.val := by omega
  have hv : 3 ≤ v.val := by omega
  rw [prop_adj] at hadj
  rcases hadj with ⟨huv, hA | hB | hC | hD⟩
  · exfalso
    omega
  · intro he
    have he' : (u.val + 1) % 2 = (v.val + 1) % 2 := Fin.mk.inj he
    have h1' : (u.val + 1) % 2 = (u.val - 3) % 2 := by
      rw [show u.val + 1 = (u.val - 3) + 4 by omega, Nat.add_mod, Nat.add_mod]
      omega
    have h2' : (v.val + 1) % 2 = (v.val - 3) % 2 := by
      rw [show v.val + 1 = (v.val - 3) + 4 by omega, Nat.add_mod, Nat.add_mod]
      omega
    have hmod : (u.val - 3) % 2 = (v.val - 3) % 2 := h1'.symm.trans (he' ▸ h2')
    have h1'' : 2 * ((u.val - 3) / 2) + (u.val - 3) % 2 = u.val - 3 := Nat.div_add_mod _ _
    have h2'' : 2 * ((v.val - 3) / 2) + (v.val - 3) % 2 = v.val - 3 := Nat.div_add_mod _ _
    omega
  · exfalso
    omega
  · exfalso
    omega

/-- **EVERY ODD CYCLE OF `prop` MEETS `C`.** -/
theorem hitsOddCycles_propC :
    ∀ D : Finset (Fin 9), IsOddCycle prop D → D ∩ propC ≠ ∅ :=
  hitsOddCycles_of_isBipartite_delete isBipartite_delete_propC

/-- **THE PETALS MEET `C` IN EXACTLY THEIR ATTACHMENT POINT.** -/
theorem inter_propT0_C : propT0 ∩ propC = {0} := by
  rw [propT0_eq, propC_eq]
  refine inter_eq_singleton (s := ({0, 3, 4} : Finset (Fin 9)))
    (t := ({0, 1, 2} : Finset (Fin 9))) (a := 0) ?_ ?_ ?_
  · intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
      first
        | exact h1
        | exact h1.symm ▸ h2
        | simp only [Fin.ext_iff] at h1 h2
          omega
  · exact mem_first_triple (0 : Fin 9) 3 4
  · exact mem_first_triple (0 : Fin 9) 1 2

theorem inter_propT1_C : propT1 ∩ propC = {1} := by
  rw [propT1_eq, propC_eq]
  refine inter_eq_singleton (s := ({1, 5, 6} : Finset (Fin 9)))
    (t := ({0, 1, 2} : Finset (Fin 9))) (a := 1) ?_ ?_ ?_
  · intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
      first
        | exact h1
        | exact h1.symm ▸ h2
        | simp only [Fin.ext_iff] at h1 h2
          omega
  · exact mem_first_triple (1 : Fin 9) 5 6
  · exact mem_mid_triple (0 : Fin 9) 1 2

theorem inter_propT2_C : propT2 ∩ propC = {2} := by
  rw [propT2_eq, propC_eq]
  refine inter_eq_singleton (s := ({2, 7, 8} : Finset (Fin 9)))
    (t := ({0, 1, 2} : Finset (Fin 9))) (a := 2) ?_ ?_ ?_
  · intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
      first
        | exact h1
        | exact h1.symm ▸ h2
        | simp only [Fin.ext_iff] at h1 h2
          omega
  · exact mem_first_triple (2 : Fin 9) 7 8
  · exact mem_last_triple (0 : Fin 9) 1 2

theorem oneAttach_propT0 : OneAttach prop propC propT0 :=
  ⟨isOddCycle_propT0, by rw [inter_propT0_C]; exact Finset.card_singleton 0⟩

theorem oneAttach_propT1 : OneAttach prop propC propT1 :=
  ⟨isOddCycle_propT1, by rw [inter_propT1_C]; exact Finset.card_singleton 1⟩

theorem oneAttach_propT2 : OneAttach prop propC propT2 :=
  ⟨isOddCycle_propT2, by rw [inter_propT2_C]; exact Finset.card_singleton 2⟩

/-- **THE ATTACHMENT SET OF `C` IN THE PROPELLER IS ALL OF `C`.** -/
theorem petalSet_propC : PetalSet prop propC = propC := by
  refine Finset.Subset.antisymm (petalSet_subset (C := propC)) ?_
  intro x hx
  rw [mem_propC_iff] at hx
  rcases hx with hx | hx | hx
  · subst hx
    exact mem_petalSet.mpr ⟨mem_first_triple (0 : Fin 9) 1 2, propT0, isOddCycle_propT0,
      inter_propT0_C⟩
  · subst hx
    exact mem_petalSet.mpr ⟨mem_mid_triple (0 : Fin 9) 1 2, propT1, isOddCycle_propT1,
      inter_propT1_C⟩
  · subst hx
    exact mem_petalSet.mpr ⟨mem_last_triple (0 : Fin 9) 1 2, propT2, isOddCycle_propT2,
      inter_propT2_C⟩

theorem card_propC : propC.card = 3 :=
  card_triple (fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 1))
    (fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 2))
    (fin_ne_val _ _ (by decide : (1 : ℕ) ≠ 2))

theorem card_petalSet_propC : (PetalSet prop propC).card = 3 := by
  rw [petalSet_propC]
  exact card_propC

/-- **THE THREE PENDANT TRIANGLES ARE PAIRWISE DISJOINT**, so they are a packing of petals. -/
theorem inter_propT0_propT1 : propT0 ∩ propT1 = ∅ := by
  rw [propT0_eq, propT1_eq]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
    simp only [Fin.ext_iff] at h1 h2 <;> omega

theorem inter_propT0_propT2 : propT0 ∩ propT2 = ∅ := by
  rw [propT0_eq, propT2_eq]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
    simp only [Fin.ext_iff] at h1 h2 <;> omega

theorem inter_propT1_propT2 : propT1 ∩ propT2 = ∅ := by
  rw [propT1_eq, propT2_eq]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
    simp only [Fin.ext_iff] at h1 h2 <;> omega

theorem inter_propT1_propT0 : propT1 ∩ propT0 = ∅ := by
  rw [propT1_eq, propT0_eq]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
    simp only [Fin.ext_iff] at h1 h2 <;> omega

theorem inter_propT2_propT0 : propT2 ∩ propT0 = ∅ := by
  rw [propT2_eq, propT0_eq]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
    simp only [Fin.ext_iff] at h1 h2 <;> omega

theorem inter_propT2_propT1 : propT2 ∩ propT1 = ∅ := by
  rw [propT2_eq, propT1_eq]
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
    simp only [Fin.ext_iff] at h1 h2 <;> omega


theorem mem_propPetals_iff {X : Finset (Fin 9)} :
    X ∈ ({propT0, propT1, propT2} : Finset (Finset (Fin 9))) ↔
      X = propT0 ∨ X = propT1 ∨ X = propT2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem mem_propT0_in_propPetals : propT0 ∈ ({propT0, propT1, propT2} : Finset (Finset (Fin 9))) := by
  rw [mem_propPetals_iff]; exact Or.inl rfl

theorem mem_propT1_in_propPetals : propT1 ∈ ({propT0, propT1, propT2} : Finset (Finset (Fin 9))) := by
  rw [mem_propPetals_iff]; exact Or.inr (Or.inl rfl)

theorem mem_propT2_in_propPetals : propT2 ∈ ({propT0, propT1, propT2} : Finset (Finset (Fin 9))) := by
  rw [mem_propPetals_iff]; exact Or.inr (Or.inr rfl)

/-- **THE THREE PENDANT TRIANGLES ARE A PACKING OF PETALS.** -/
theorem disjointFamily_propPetals :
    DisjointFamily ({propT0, propT1, propT2} : Finset (Finset (Fin 9))) := by
  intro X hX Y hY hne
  rw [mem_propPetals_iff] at hX
  rw [mem_propPetals_iff] at hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact inter_propT0_propT1
  · exact inter_propT0_propT2
  · exact inter_propT1_propT0
  · exact absurd rfl hne
  · exact inter_propT1_propT2
  · exact inter_propT2_propT0
  · exact inter_propT2_propT1
  · exact absurd rfl hne

theorem all_isOddCycle_propPetals :
    ∀ X ∈ ({propT0, propT1, propT2} : Finset (Finset (Fin 9))), IsOddCycle prop X := by
  intro X hX
  rw [mem_propPetals_iff] at hX
  rcases hX with rfl | rfl | rfl
  · exact isOddCycle_propT0
  · exact isOddCycle_propT1
  · exact isOddCycle_propT2

theorem isOddCycleFamily_propPetals :
    IsOddCycleFamily (G := prop) ({propT0, propT1, propT2} : Finset (Finset (Fin 9))) :=
  ⟨disjointFamily_propPetals, all_isOddCycle_propPetals⟩

/-- **THE PACKING OF PETALS COVERS THE ATTACHMENT SET** — the hypothesis of the new instance,
realised on a concrete graph. -/
theorem prop_petalPackingCover :
    PetalSet prop propC ⊆ ({propT0, propT1, propT2} : Finset (Finset (Fin 9))).biUnion id := by
  intro x hx
  rw [petalSet_propC, mem_propC_iff] at hx
  rcases hx with hx | hx | hx
  · subst hx
    exact Finset.mem_biUnion.mpr ⟨propT0, mem_propT0_in_propPetals, mem_first_triple 0 3 4⟩
  · subst hx
    exact Finset.mem_biUnion.mpr ⟨propT1, mem_propT1_in_propPetals, mem_first_triple 1 5 6⟩
  · subst hx
    exact Finset.mem_biUnion.mpr ⟨propT2, mem_propT2_in_propPetals, mem_first_triple 2 7 8⟩

theorem oneAttach_of_mem_propPetals {D : Finset (Fin 9)}
    (hD : D ∈ ({propT0, propT1, propT2} : Finset (Finset (Fin 9)))) : OneAttach prop propC D := by
  rw [mem_propPetals_iff] at hD
  rcases hD with rfl | rfl | rfl
  · exact oneAttach_propT0
  · exact oneAttach_propT1
  · exact oneAttach_propT2

/-- **THE MAXIMUM DEFICIENCY OF THE PROPELLER IS EXACTLY 3.** -/
theorem maxDef_prop : MaxDef prop = 3 := by
  have h1 : MaxDef prop ≤ 3 := maxDef_le_of_locIndep locIndep_three_prop
  have h2 : ¬ MaxDef prop ≤ 2 :=
    fun h => not_locIndep_two_prop ((locIndep_iff_maxDef_le (G := prop)).mpr h)
  omega

/-- **`CloseToBipartite 3 prop`**: deleting `C` leaves the matching `3 - 4`, `5 - 6`, `7 - 8`. -/
theorem closeToBipartite_three_prop : CloseToBipartite 3 prop :=
  ⟨propC, by rw [card_propC], isBipartite_delete_propC⟩

/-- **AND NOT TWO VERTICES:** the odd cycle transversal number of the propeller is exactly `3`. -/
theorem not_closeToBipartite_two_prop : ¬ CloseToBipartite 2 prop := by
  intro h
  have hmd := maxDef_le_closeToBipartite h
  rw [maxDef_prop] at hmd
  omega

theorem petalSet_propC_ne_empty : PetalSet prop propC ≠ ∅ := by
  rw [petalSet_propC]
  intro h
  have hc := card_propC
  rw [h, Finset.card_empty] at hc
  omega

/-- **THE PETAL TERM OF ROUND 119 CANNOT BE DROPPED.**  The propeller satisfies the residue hypothesis
of `JSP90.closeToBipartite_of_petalSet` (every odd cycle meets `C`), its attachment set is
**non-empty** (`petalSet_propC_ne_empty`), yet it is **not** `(|C| - 1) = 2` close to bipartite.  So the
`|C| - 1` bound of `JSP90.closeToBipartite_of_petalSet_empty` — and with it the two-attachment
transversal of round 111 — genuinely needs its hypothesis, and the attachment points of `C` are
exactly what must be paid for. -/
theorem not_closeToBipartite_two_prop_of_cardC :
    ¬ CloseToBipartite (propC.card - 1) prop := by
  rw [card_propC]
  exact not_closeToBipartite_two_prop

/-- **THE NEW INSTANCE ON THE PROPELLER**: `LocIndep 3 prop` + the packing cover of the attachment
set give `CloseToBipartite (3 + |C| - 1) = CloseToBipartite 5 prop`. -/
theorem erdos73On_propeller : CloseToBipartite (3 + (propC.card - 1)) prop :=
  closeToBipartite_of_petalPackingCover isOddCycle_propC hitsOddCycles_propC
    (fun D hD => oneAttach_of_mem_propPetals (D := D) hD) isOddCycleFamily_propPetals
      prop_petalPackingCover
    locIndep_three_prop

theorem closeToBipartite_five_prop : CloseToBipartite 5 prop := by
  have h := erdos73On_propeller
  rw [card_propC] at h
  exact h

/-- **AND THE CLASS-LEVEL STATEMENT IS REALISED**: `prop` has an odd cycle `C` of three vertices
meeting every odd cycle, whose attachment set is charged against its deficiency. -/
theorem oneCyclePetal_prop : OneCyclePetal prop propC.card := by
  refine ⟨propC, isOddCycle_propC, le_rfl, hitsOddCycles_propC, ?_⟩
  rw [card_petalSet_propC, maxDef_prop]

end Propeller

/-! ### Part 5 — the seven-vertex `g7`: the attachment set is LARGER than the deficiency -/

section G7

/-- The triangle `C = {0, 1, 2}` of `g7`. -/
def g7C : Finset (Fin 7) := {0, 1, 2}

/-- The petal `{0, 3, 4}` of `g7C`. -/
def g7T0 : Finset (Fin 7) := {0, 3, 4}

/-- The petal `{1, 3, 5}` of `g7C`. -/
def g7T1 : Finset (Fin 7) := {1, 3, 5}

/-- The petal `{2, 3, 6}` of `g7C`. -/
def g7T2 : Finset (Fin 7) := {2, 3, 6}

theorem g7C_eq : g7C = ({0, 1, 2} : Finset (Fin 7)) := rfl

theorem g7T0_eq : g7T0 = ({0, 3, 4} : Finset (Fin 7)) := rfl

theorem g7T1_eq : g7T1 = ({1, 3, 5} : Finset (Fin 7)) := rfl

theorem g7T2_eq : g7T2 = ({2, 3, 6} : Finset (Fin 7)) := rfl

theorem mem_g7C_iff {x : Fin 7} : x ∈ g7C ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  rw [g7C_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem isOddCycle_g7C : IsOddCycle g7 g7C := by
  refine isOddCycle_triple g7 g7cyc012_inj g7cyc012_cyc rfl rfl rfl

theorem isOddCycle_g7T0 : IsOddCycle g7 g7T0 := by
  refine isOddCycle_triple g7 g7cyc034_inj g7cyc034_cyc rfl rfl rfl

theorem isOddCycle_g7T1 : IsOddCycle g7 g7T1 := by
  refine isOddCycle_triple g7 g7cyc135_inj g7cyc135_cyc rfl rfl rfl

theorem isOddCycle_g7T2 : IsOddCycle g7 g7T2 := by
  refine isOddCycle_triple g7 g7cyc236_inj g7cyc236_cyc rfl rfl rfl

theorem inter_g7T0_C : g7T0 ∩ g7C = {0} := by
  rw [g7T0_eq, g7C_eq]
  refine inter_eq_singleton (s := ({0, 3, 4} : Finset (Fin 7)))
    (t := ({0, 1, 2} : Finset (Fin 7))) (a := 0) ?_ ?_ ?_
  · intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
      first
        | exact h1
        | exact h1.symm ▸ h2
        | simp only [Fin.ext_iff] at h1 h2
          omega
  · exact mem_first_triple (0 : Fin 7) 3 4
  · exact mem_first_triple (0 : Fin 7) 1 2

theorem inter_g7T1_C : g7T1 ∩ g7C = {1} := by
  rw [g7T1_eq, g7C_eq]
  refine inter_eq_singleton (s := ({1, 3, 5} : Finset (Fin 7)))
    (t := ({0, 1, 2} : Finset (Fin 7))) (a := 1) ?_ ?_ ?_
  · intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
      first
        | exact h1.symm ▸ h2
        | simp only [Fin.ext_iff] at h1 h2
          omega
  · exact mem_first_triple (1 : Fin 7) 3 5
  · exact mem_mid_triple (0 : Fin 7) 1 2

theorem inter_g7T2_C : g7T2 ∩ g7C = {2} := by
  rw [g7T2_eq, g7C_eq]
  refine inter_eq_singleton (s := ({2, 3, 6} : Finset (Fin 7)))
    (t := ({0, 1, 2} : Finset (Fin 7))) (a := 2) ?_ ?_ ?_
  · intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with h1 | h1 | h1 <;> rcases hx2 with h2 | h2 | h2 <;>
      first
        | exact h1.symm ▸ h2
        | simp only [Fin.ext_iff] at h1 h2
          omega
  · exact mem_first_triple (2 : Fin 7) 3 6
  · exact mem_last_triple (0 : Fin 7) 1 2

theorem oneAttach_g7T0 : OneAttach g7 g7C g7T0 :=
  ⟨isOddCycle_g7T0, by rw [inter_g7T0_C]; exact Finset.card_singleton 0⟩

theorem oneAttach_g7T1 : OneAttach g7 g7C g7T1 :=
  ⟨isOddCycle_g7T1, by rw [inter_g7T1_C]; exact Finset.card_singleton 1⟩

theorem oneAttach_g7T2 : OneAttach g7 g7C g7T2 :=
  ⟨isOddCycle_g7T2, by rw [inter_g7T2_C]; exact Finset.card_singleton 2⟩

/-- **THE ATTACHMENT SET OF `C` IN `g7` IS ALL OF `C`.**  Every vertex of the triangle is the
attachment point of a petal, so `|PetalSet g7 C| = 3 = |C|`: no hypothesis can make the attachment set
smaller here. -/
theorem petalSet_g7C : PetalSet g7 g7C = g7C := by
  refine Finset.Subset.antisymm (petalSet_subset (C := g7C)) ?_
  intro x hx
  rw [mem_g7C_iff] at hx
  rcases hx with hx | hx | hx
  · subst hx
    exact mem_petalSet.mpr ⟨mem_first_triple (0 : Fin 7) 1 2, g7T0, isOddCycle_g7T0, inter_g7T0_C⟩
  · subst hx
    exact mem_petalSet.mpr ⟨mem_mid_triple (0 : Fin 7) 1 2, g7T1, isOddCycle_g7T1, inter_g7T1_C⟩
  · subst hx
    exact mem_petalSet.mpr ⟨mem_last_triple (0 : Fin 7) 1 2, g7T2, isOddCycle_g7T2, inter_g7T2_C⟩

theorem card_g7C : g7C.card = 3 :=
  card_triple (fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 1))
    (fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 2))
    (fin_ne_val _ _ (by decide : (1 : ℕ) ≠ 2))

theorem card_petalSet_g7C : (PetalSet g7 g7C).card = 3 := by
  rw [petalSet_g7C]
  exact card_g7C

/-- **THE MAXIMUM DEFICIENCY OF `g7` IS EXACTLY 2.** -/
theorem maxDef_g7 : MaxDef g7 = 2 := by
  have h1 : MaxDef g7 ≤ 2 := maxDef_le_of_locIndep locIndep_two_g7
  have h2 : ¬ MaxDef g7 ≤ 1 :=
    fun h => not_locIndep_one_g7 ((locIndep_iff_maxDef_le (G := g7)).mpr h)
  omega

/-- **THE NEGATIVE RESULT OF ROUND 120: THE ATTACHMENT SET IS NOT CHARGED AGAINST THE DEFICIENCY.**
In `g7` the attachment set has three vertices while the deficiency is two, so

* `|PetalSet G C| ≤ MaxDef G` is **false**;
* hence so is `|PetalSet G C| ≤ MaxDef G / 2`, and so is any bound of the form `c * MaxDef G` with
  `c < 3 / 2`.

Any function `phi` with `|PetalSet G C| ≤ phi (MaxDef G)` must therefore satisfy `phi 2 ≥ 3`: the
round-119 numerical blocker cannot be closed by comparing the attachment set with the deficiency of
`G`. -/
theorem not_petalSet_le_maxDef_g7 : ¬ ((PetalSet g7 g7C).card ≤ MaxDef g7) := by
  intro h
  rw [card_petalSet_g7C, maxDef_g7] at h
  omega

/-- **THE PETALS OF `g7` ALL MEET IN THE VERTEX `3`**, so no two of them are disjoint: they cannot form
a packing, which is consistent with `not_petalSet_le_maxDef_g7` — the packing-cover hypothesis of
`JSP90.card_petalSet_le_maxDef_of_cover` really is extra content. -/
theorem not_inter_empty_g7T0_g7T1 : g7T0 ∩ g7T1 ≠ ∅ := by
  rw [g7T0_eq, g7T1_eq]
  exact fun h => (Finset.not_nonempty_iff_eq_empty.mpr h) ⟨3, Finset.mem_inter.mpr ⟨by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl True.intro), by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl True.intro)⟩⟩

/-- **THE THREE PETALS OF `g7` ARE NOT A PACKING OF ODD CYCLES.** -/
theorem not_oddCycleFamily_g7Petals :
    ¬ IsOddCycleFamily (G := g7) ({g7T0, g7T1, g7T2} : Finset (Finset (Fin 7))) := by
  rintro ⟨hdisj, -⟩
  have hne : g7T0 ≠ g7T1 := by
    intro h
    have h0 : (0 : Fin 7) ∈ g7T1 := h ▸ mem_first_triple (0 : Fin 7) 3 4
    rw [g7T1_eq] at h0
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0
    rcases h0 with h0' | h0' | h0'
    · exact fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 1) h0'
    · exact fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 3) h0'
    · exact fin_ne_val _ _ (by decide : (0 : ℕ) ≠ 5) h0'
  have hmem0 : g7T0 ∈ ({g7T0, g7T1, g7T2} : Finset (Finset (Fin 7))) := by
    rw [show ({g7T0, g7T1, g7T2} : Finset (Finset (Fin 7))) =
      insert g7T0 (insert g7T1 (insert g7T2 ∅)) from rfl]
    exact Finset.mem_insert_self g7T0 _
  have hmem1 : g7T1 ∈ ({g7T0, g7T1, g7T2} : Finset (Finset (Fin 7))) := by
    rw [show ({g7T0, g7T1, g7T2} : Finset (Finset (Fin 7))) =
      insert g7T0 (insert g7T1 (insert g7T2 ∅)) from rfl]
    exact Finset.mem_insert_of_mem (a := g7T1) (b := g7T0) (Finset.mem_insert_self g7T1 _)
  exact not_inter_empty_g7T0_g7T1 (hdisj g7T0 hmem0 g7T1 hmem1 hne)

end G7

end

end JSP90
