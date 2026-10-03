import JSPProblem.AttachPoints
import Mathlib.Data.Finset.SDiff

/-!
# JSP-000090, round 137 — `JSPProblem/Segment.lean`: **the segments of an odd cycle inside a shortest
# odd cycle**, and a *tighter* residual for the sharp case `k = 1`

Attack family 66.  Round 136 (`JSPProblem/AttachPoints.lean`) introduced the **attachment points**

```lean
attachPoints G C = ⋃ (y ∈ boundary G C) (attachSet G C y) = { a ∈ C : a has a neighbour in the fan }
```

and proved that they are an odd-cycle transversal (`JSP90.hitsOddCycles_attachPoints_of_packing_one`),
with instances of constants `|attachPoints|`, `1` and `2`, the last being the optimal constant of
Erdős Problem #73 at `k = 1`.  The residual of the sharp case became

```lean
JSP90.AttachThreeResidual : LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
                            ∃ X, |X| ≤ 2 ∧ X meets every odd cycle of G
```

## The new object: the *segments* of `D ∩ C`

Let `C` be a shortest odd cycle, `D ≠ C` an odd cycle, and let `o` be the cyclic numbering of `D`.
Reading the vertices of `D` in order, those lying on `C` come in **maximal segments** — maximal runs of
consecutive indices with `o.f i ∈ C`.  The classical fact is

> **each segment has both ends in the attachment points of `C`.**

Indeed the end `i` of a segment has a `D`-neighbour outside the segment, hence outside `C`, i.e. a
fan vertex; so `o.f i` is an attachment point.  This is the *exit* point
`JSP90.mem_attachPoints_exit` of Part 1; the *entry* point `JSP90.mem_attachPoints_entry` is the same
statement at the other end of a gap.  Part 2 turns it into the counting statement

| statement | meaning |
| --- | --- |
| **`JSP90.two_le_card_attachPoints_inter_of_card_inter_ge_two`** | **`2 ≤ |C ∩ D| ⟹ 2 ≤ |attachPoints G C ∩ D|`** |
| **`JSP90.two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one`** | the same, at packing number one, when no odd cycle meets `C` in exactly one point |

so a *single* intersection point `C ∩ D = {a}` is the only obstruction.

The single obstruction is a segment of length `0`, i.e. **a one-point cross-over** `C ∩ D = {a}`: it
contributes exactly one attachment point, and `discovery/JSP-000090/r137.c` (question `Q1`, no
failures over the `986 787` graphs with `LocIndep 1` on `n ≤ 7` vertices) confirms the theorem, while
question `Q4` shows the converse fails in general (`63 720` counterexamples): the cross-over vertex
need not be a transversal.

## Part 4 — the instances: no cross-over means attachment points suffice

Under the **no-cross-over** hypothesis `JSP90.NoCrossOver G C`, every odd cycle meets the attachment
points in **two** points, so

* **`JSP90.hitsOddCycles_erase_of_attachPoints_of_noCrossOver`** —
  `attachPoints G C ∖ {a}` meets every odd cycle of `G`, for every `a ∈ attachPoints G C`;
* `|attachPoints G C| = 2` gives `CloseToBipartite 1 G`, the **optimal** constant at `k = 1`;
* `|attachPoints G C| = 3` gives `CloseToBipartite 2 G` with **any pair** of attachment points as the
  certificate (`JSP90.hitsOddCycles_pair_of_noCrossOver_of_card_attachPoints_eq_three`).

## Part 5 — the tighter residual

The exhaustive search (`r137.c`, question `Q6`) shows that in the residual case
`min_C |attachPoints G C| ≥ 3` the certificate can **always be taken inside the attachment points of a
shortest odd cycle** (all `258 550` residual graphs on `n ≤ 7`), so the residual is now

```lean
JSP90.AttachThreeResidualRefined : … → 3 ≤ |attachPoints G C| →
                                    ∃ a b, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
                                           HitsOddCycles G {a, b}
```

`JSP90.attachThreeResidual_of_attachThreeResidualRefined` makes the comparison with round 136 formal and
`JSP90.erdos73On_one_two_of_attachThreeResidualRefined` proves that it still yields the **sharp**
`Erdős73On 1 2`.  The optimality of that constant is machine-checked on six vertices in
`JSPProblem/SharpTwo.lean`.

## What is *not* proved

`JSP90.AttachThreeResidualRefined`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is not declared, so
the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 400000

local instance segmentDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 1 — the two ends of a segment are attachment points -/

section Segment

variable {C D : Finset V}

/-- **AN EXIT POINT IS AN ATTACHMENT POINT.**  If `o.f i` lies on `C` and its successor along the cycle
`D` does not, then that successor is a fan vertex of `C` attached to `o.f i`, so
`o.f i ∈ attachPoints G C`.

This is the *exit* end of a segment of `C` along `D`. -/
theorem mem_attachPoints_exit {o : CycleOrder G D} {i : Fin o.m} (hiC : o.f i ∈ C)
    (hsucc : o.f (cycSucc i) ∉ C) : o.f i ∈ attachPoints G C := by
  have hadj : G.Adj (o.f i) (o.f (cycSucc i)) := o.hcyc i
  refine mem_attachPoints.mpr ⟨hiC, o.f (cycSucc i), ?_, hadj⟩
  exact mem_boundary.mpr ⟨hsucc, o.f i, hiC, hadj.symm⟩

/-- **AN ENTRY POINT IS AN ATTACHMENT POINT**, the mirror image of `JSP90.mem_attachPoints_exit`: if
`o.f i` is off `C` and its successor along `D` is on `C`, then `o.f i` is a fan vertex attached to
`o.f (cycSucc i)`, so the latter is an attachment point. -/
theorem mem_attachPoints_entry {o : CycleOrder G D} {i : Fin o.m} (hi : o.f i ∉ C)
    (hsucc : o.f (cycSucc i) ∈ C) : o.f (cycSucc i) ∈ attachPoints G C := by
  have hadj : G.Adj (o.f i) (o.f (cycSucc i)) := o.hcyc i
  refine mem_attachPoints.mpr
    ⟨hsucc, o.f i, mem_boundary.mpr ⟨hi, o.f (cycSucc i), hsucc, hadj⟩, hadj.symm⟩

/-- **`D` IS NOT CONTAINED IN `C`** when `C` is a *shortest* odd cycle and `D ≠ C`: otherwise
`JSP90.eq_of_isOddCycle_subset_shortest` would give `D = C`. -/
theorem not_subset_of_isOddCycle_ne_of_shortest {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hD : IsOddCycle G D)
    (hne : D ≠ C) : ¬ D ⊆ C := by
  intro hsub
  exact hne (eq_of_isOddCycle_subset_shortest hC hshort hD hsub)

/-- **THE EXIT OF THE SEGMENT OF `C` ALONG `D` CONTAINING `i`.**

If `o.f i ∈ C` and some vertex of `D` lies off `C`, then walking forward along `D` from `i` one
leaves `C` at some step `k ≥ 1`, and the vertex just before that step,
`e = cycSucc^[k - 1] i`, is an **attachment point of `C`** (`JSP90.mem_attachPoints_exit`).  Every step
before `k` stays on `C`, which is what the last conjunct records; this is the only information about
the walk which the counting theorem of Part 2 needs. -/
theorem exists_exit_of_mem_of_exists_not_mem {o : CycleOrder G D} {i : Fin o.m} (hiC : o.f i ∈ C)
    {t0 : Fin o.m} (ht0 : o.f t0 ∉ C) :
    ∃ (k : ℕ) (e : Fin o.m), 1 ≤ k ∧ e = ((cycSucc^[k - 1] : Fin o.m → Fin o.m) i) ∧
      o.f e ∈ attachPoints G C ∧
      (∀ t : ℕ, t < k → o.f ((cycSucc^[t] : Fin o.m → Fin o.m) i) ∈ C) := by
  classical
  obtain ⟨k0, _, hk0t0⟩ := o.exists_iter i t0
  set P : ℕ → Prop := fun t => o.f ((cycSucc^[t] : Fin o.m → Fin o.m) i) ∉ C with hP
  have hexP : ∃ t, P t := ⟨k0, by simp [P, hk0t0, ht0]⟩
  set k : ℕ := Nat.find hexP with hkdef
  have hkP : P k := by
    rw [hkdef]
    exact Nat.find_spec hexP
  have hP0 : ¬ P 0 := by
    show ¬ ¬ o.f ((cycSucc^[0] : Fin o.m → Fin o.m) i) ∈ C
    intro h
    exact h (by simpa only [Function.iterate_zero, id_eq] using hiC)
  have hkpos : 0 < k := by
    rw [hkdef]
    exact Nat.pos_of_ne_zero fun hc => hP0 (hc ▸ Nat.find_spec hexP)
  have hkmin : ∀ t : ℕ, t < k → o.f ((cycSucc^[t] : Fin o.m → Fin o.m) i) ∈ C := by
    intro t ht
    by_contra hcon
    have hle : Nat.find hexP ≤ t := Nat.find_min' hexP hcon
    omega
  have hstep : cycSucc ((cycSucc^[k - 1] : Fin o.m → Fin o.m) i)
      = ((cycSucc^[k] : Fin o.m → Fin o.m) i) := by
    have h1 := o.iter_succ i (k - 1)
    rw [Nat.sub_add_cancel hkpos] at h1
    exact h1.symm
  have hle : k - 1 < k := by omega
  refine ⟨k, (cycSucc^[k - 1] : Fin o.m → Fin o.m) i, hkpos, rfl, ?_, hkmin⟩
  exact mem_attachPoints_exit (hkmin (k - 1) hle) (by rw [hstep]; exact hkP)

/-- **THE ENTRY OF THE FIRST SEGMENT OF `C` ALONG `D` AFTER `t0`.**  The mirror image of the
preceding theorem: walking forward from a vertex `t0` off `C`, one meets `C` at some step `l`, and the
vertex just before that step, `a`, is off `C` while `o.f (cycSucc a)` is an **attachment point of
`C`**. -/
theorem exists_entry_of_not_mem_of_exists_mem {o : CycleOrder G D} {t0 : Fin o.m} (ht0 : o.f t0 ∉ C)
    {i : Fin o.m} (hiC : o.f i ∈ C) :
    ∃ (a : Fin o.m) (l : ℕ), o.f a ∉ C ∧ o.f (cycSucc a) ∈ attachPoints G C := by
  classical
  obtain ⟨l0, _, hl0i⟩ := o.exists_iter t0 i
  set Q : ℕ → Prop := fun t => o.f ((cycSucc^[t] : Fin o.m → Fin o.m) t0) ∈ C with hQ
  have hexQ : ∃ t, Q t := ⟨l0, by simp [Q, hl0i, hiC]⟩
  set l : ℕ := Nat.find hexQ with hldef
  have hlQ : Q l := by
    rw [hldef]
    exact Nat.find_spec hexQ
  have hQ0 : ¬ Q 0 := by
    show ¬ o.f ((cycSucc^[0] : Fin o.m → Fin o.m) t0) ∈ C
    simpa only [Function.iterate_zero, id_eq] using ht0
  have hlpos : 0 < l := by
    rw [hldef]
    exact Nat.pos_of_ne_zero fun hc => hQ0 (hc ▸ Nat.find_spec hexQ)
  have hlmin : ∀ t : ℕ, t < l → o.f ((cycSucc^[t] : Fin o.m → Fin o.m) t0) ∉ C := by
    intro t ht
    by_contra hcon
    have hle : Nat.find hexQ ≤ t := Nat.find_min' hexQ hcon
    omega
  have hstep : cycSucc ((cycSucc^[l - 1] : Fin o.m → Fin o.m) t0)
      = ((cycSucc^[l] : Fin o.m → Fin o.m) t0) := by
    have h1 := o.iter_succ t0 (l - 1)
    rw [Nat.sub_add_cancel hlpos] at h1
    exact h1.symm
  have hle : l - 1 < l := by omega
  refine ⟨(cycSucc^[l - 1] : Fin o.m → Fin o.m) t0, l, hlmin (l - 1) hle, ?_⟩
  exact mem_attachPoints_entry (hlmin (l - 1) hle) (by rw [hstep]; exact hlQ)

/-- A set containing two distinct vertices has at least two elements. -/
theorem two_le_card_of_mem_pair {S : Finset V} {p q : V} (hne : p ≠ q) (hp : p ∈ S) (hq : q ∈ S) :
    2 ≤ S.card := by
  have h2c : ({p, q} : Finset V).card = 2 := by
    have he : ({p, q} : Finset V) = insert p ({q} : Finset V) := rfl
    rw [he, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  calc 2 = ({p, q} : Finset V).card := h2c.symm
    _ ≤ S.card := Finset.card_le_card fun z hz => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp
      · exact hq

/-- A set of at least two elements contains two distinct elements. -/
theorem exists_pair_ne_of_card_ge_two {S : Finset V} (h2 : 2 ≤ S.card) :
    ∃ a b : V, a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  have hne0 : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    have hz : S.card = 0 := Finset.card_eq_zero.mpr hcon
    omega
  obtain ⟨a, ha⟩ := hne0
  have herase : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
  have hne1 : (S.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    have hz : (S.erase a).card = 0 := Finset.card_eq_zero.mpr hcon
    omega
  obtain ⟨b, hb⟩ := hne1
  exact ⟨a, b, ha, Finset.mem_of_mem_erase hb, Ne.symm (Finset.mem_erase.mp hb).1⟩

/-! ## Part 2 — two attachment points, unless there is a one-point cross-over -/

/-- **AN ODD CYCLE OTHER THAN `C` MEETS THE ATTACHMENT POINTS OF `C` IN AT LEAST TWO POINTS, AS SOON AS
IT MEETS `C` IN AT LEAST TWO POINTS.**

```lean
2 ≤ (C ∩ D).card  ⟹  2 ≤ (attachPoints G C ∩ D).card
```

Proof, with `o` the cyclic numbering of `D`.  Two vertices of `D` lie on `C`, at distinct indices
`i ≠ j`; some vertex `t₀` of `D` lies off `C` (else `D ⊆ C` and, `C` being shortest, `D = C`).
Walking forward along `D`:

* from `i` one leaves `C` at some step `k ≥ 1`, and the vertex `o.f e` just before it, `e` the
  `k - 1`-st iterate, is an attachment point (`JSP90.exists_exit_of_mem_of_exists_not_mem`);
* from `t₀` one meets `C` at some step `l ≥ 1`, and the vertex `o.f (cycSucc a)` just after the last
  step outside `C` is an attachment point (`JSP90.exists_entry_of_not_mem_of_exists_mem`).

If the two indices differ we are done.  If `e = cycSucc a` then `a ∉ C`, `cycSucc a ∈ C` and
`cycSucc (cycSucc a) ∉ C`, i.e. the segment of `C` along `D` through `e` is the *single* vertex `e`.
Take a vertex of `D` on `C` other than `e` — there is one, `i ≠ j` — and walk forward from it to its
exit `e'`.  If `e' = e` then, since `e = cycSucc a`, the walk passes through
`a = o.prev e = o.prev (cycSucc^[k - 1] i) = cycSucc^[k - 2] i` (`JSP90.cycleOrder.prev_iter`,
`JSP90.cycleOrder.prev_succ`), which lies on `C` by the minimality of `k` — against `a ∉ C`.  So
`e' ≠ e` and the two attachment points `o.f e`, `o.f e'` finish the proof. -/
theorem two_le_card_attachPoints_inter_of_card_inter_ge_two {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hD : IsOddCycle G D)
    (hne : D ≠ C) (h2 : 2 ≤ (C ∩ D).card) : 2 ≤ (attachPoints G C ∩ D).card := by
  obtain ⟨o, -⟩ := hD.cycleOrder
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_ne_of_card_ge_two h2
  obtain ⟨i, hi⟩ := (o.hmem x).mp (Finset.mem_inter.mp hx).2
  obtain ⟨j, hj⟩ := (o.hmem y).mp (Finset.mem_inter.mp hy).2
  have hij : i ≠ j := fun h => hxy (by rw [← hi, ← hj, h])
  have hiC : o.f i ∈ C := by rw [hi]; exact (Finset.mem_inter.mp hx).1
  have hjC : o.f j ∈ C := by rw [hj]; exact (Finset.mem_inter.mp hy).1
  obtain ⟨t0, ht0⟩ : ∃ t0 : Fin o.m, o.f t0 ∉ C := by
    by_contra hcon
    have hall : ∀ t0 : Fin o.m, o.f t0 ∈ C := fun t0 => by
      by_contra hn
      exact hcon ⟨t0, hn⟩
    exact not_subset_of_isOddCycle_ne_of_shortest hC hshort hD hne fun z hz => by
      obtain ⟨t, rfl⟩ := (o.hmem z).mp hz
      exact hall t
  obtain ⟨k, e, hkpos, _, hpe, hkmin⟩ := exists_exit_of_mem_of_exists_not_mem hiC ht0
  obtain ⟨a, _, ha', hpa⟩ := exists_entry_of_not_mem_of_exists_mem ht0 hiC
  by_cases hneEA : e = cycSucc a
  · -- the segment of `C` along `D` through `e` is the single vertex `e`: a second vertex of `D` on
    -- `C` gives a second, different exit
    have hprev : o.prev e = a := by rw [hneEA]; exact o.prev_succ a
    have key : ∀ (i2 : Fin o.m), o.f i2 ∈ C → i2 ≠ e → 2 ≤ (attachPoints G C ∩ D).card := by
      intro i2 hi2C hi2ne
      obtain ⟨k2, e2, hk2pos, he2eq, hpe2, hk2min⟩ := exists_exit_of_mem_of_exists_not_mem hi2C ht0
      have hne2 : e2 ≠ e := by
        intro hEE
        by_cases hk2one : k2 = 1
        · have hie2 : e2 = i2 := by rw [he2eq, hk2one]; simp
          exact hi2ne (hie2.symm.trans hEE)
        · have hk2ge : 2 ≤ k2 := by omega
          have h1 : o.prev ((cycSucc^[k2 - 1] : Fin o.m → Fin o.m) i2) = o.prev e := by
            rw [← hEE, he2eq]
          have haeq : a = ((cycSucc^[k2 - 2] : Fin o.m → Fin o.m) i2) := by
            rw [← hprev, ← h1, o.prev_iter i2 (by omega)]
            congr 1
          rw [haeq] at ha'
          exact ha' (hk2min (k2 - 2) (by omega))
      have hne2' : o.f e2 ≠ o.f e := fun h => hne2 (o.hinj h)
      exact two_le_card_of_mem_pair (S := attachPoints G C ∩ D) hne2'
        (mem_inter.mpr ⟨hpe2, (o.hmem _).mpr ⟨e2, rfl⟩⟩)
        (mem_inter.mpr ⟨hpe, (o.hmem _).mpr ⟨e, rfl⟩⟩)
    by_cases hie : i = e
    · exact key j hjC (fun h => hij (hie.trans h.symm))
    · exact key i hiC hie
  · have hne' : o.f (cycSucc a) ≠ o.f e := fun h => hneEA (o.hinj h).symm
    exact two_le_card_of_mem_pair (S := attachPoints G C ∩ D) hne'
      (mem_inter.mpr ⟨hpa, (o.hmem _).mpr ⟨cycSucc a, rfl⟩⟩)
      (mem_inter.mpr ⟨hpe, (o.hmem _).mpr ⟨e, rfl⟩⟩)

/-- **NO ONE-POINT CROSS-OVER** for the shortest odd cycle `C`: no odd cycle of `G` other than `C`
itself meets `C` in exactly one vertex. -/
def NoCrossOver (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ D : Finset V, IsOddCycle G D → D ≠ C → (C ∩ D).card ≠ 1

/-- **A SET OF AT LEAST TWO ELEMENTS SURVIVES THE REMOVAL OF ONE POINT.** -/
theorem exists_mem_sdiff_singleton_of_card_ge_two {S : Finset V} (h2 : 2 ≤ S.card) {a : V} :
    (S \ {a}).Nonempty := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_ne_of_card_ge_two h2
  by_cases hxa : x ∈ ({a} : Finset V)
  · have hxa' : x = a := Finset.mem_singleton.mp hxa
    refine ⟨y, Finset.mem_sdiff.mpr ⟨hy, fun hya => ?_⟩⟩
    have hya' : y = a := Finset.mem_singleton.mp hya
    exact hxy (hxa'.trans hya'.symm)
  · refine ⟨x, Finset.mem_sdiff.mpr ⟨hx, fun h => hxa h⟩⟩

/-- **UNDER NO CROSS-OVER, EVERY ODD CYCLE MEETS THE ATTACHMENT POINTS IN TWO POINTS.**  At packing
number one, an odd cycle `D ≠ C` meets `C` (else two vertex-disjoint odd cycles), and by hypothesis it
does not meet `C` in exactly one point, so Part 2 applies. -/
theorem two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one (h : PackingNumberOne G)
    {C D : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (hD : IsOddCycle G D) (hne : D ≠ C) : 2 ≤ (attachPoints G C ∩ D).card := by
  have hne' : (C ∩ D).card ≠ 0 := fun hc => by
    have hcon : C ∩ D = ∅ := Finset.card_eq_zero.mp hc
    exact h D C hD hC (by rw [Finset.inter_comm]; exact hcon)
  have hne'' : (C ∩ D).card ≠ 1 := fun h => hnc D hD hne h
  have h2 : 2 ≤ (C ∩ D).card := by omega
  exact two_le_card_attachPoints_inter_of_card_inter_ge_two hC hshort hD hne h2

/-! ## Part 4 — the instances: no cross-over means attachment points suffice -/

/-- **UNDER NO CROSS-OVER, THE ATTACHMENT POINTS WITH ONE POINT REMOVED MEET EVERY ODD CYCLE.**

```lean
HitsOddCycles G (attachPoints G C \ {a})
```

for every `a ∈ attachPoints G C`, provided the attachment points are at least two.  This is the main
new instance of the headline theorem: the constant is `|attachPoints G C| - 1`, the certificate lies
**on the shortest odd cycle**, and only `JSP90.PackingNumberOne` is used, so it holds for every `k`
satisfying the packing condition. -/
theorem hitsOddCycles_erase_of_attachPoints_of_noCrossOver (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) {a : V} (ha : a ∈ attachPoints G C)
    (h2 : 2 ≤ (attachPoints G C).card) : HitsOddCycles G (attachPoints G C \ {a}) := by
  intro D hD
  by_cases hDC : D = C
  · rw [hDC]
    obtain ⟨x, hx⟩ := exists_mem_sdiff_singleton_of_card_ge_two (a := a) h2
    have hxA : x ∈ attachPoints G C := (Finset.mem_sdiff.mp hx).1
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr
      ⟨(mem_attachPoints.mp hxA).1, hx⟩⟩
  · obtain ⟨x, hx⟩ := exists_mem_sdiff_singleton_of_card_ge_two (a := a)
      (two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one h hC hshort hnc hD hDC)
    have hx2 : x ∈ attachPoints G C ∩ D := by
      rcases Finset.mem_sdiff.mp hx with ⟨h1, -⟩
      exact h1
    have hxD : x ∈ D := (Finset.mem_inter.mp hx2).2
    have hxm : x ∈ attachPoints G C \ {a} := by
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx2).1, ?_⟩
      intro hcon
      exact (Finset.mem_sdiff.mp hx).2 hcon
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr ⟨hxD, hxm⟩⟩

/-- **THE CONCLUSION OF ERDŐS #73 WITH THE CONSTANT `|attachPoints G C| - 1`, FOR EVERY `k`, UNDER THE
PACKING CONDITION AND NO CROSS-OVER.** -/
theorem closeToBipartite_of_noCrossOver {m : ℕ} {k : ℕ} (_hG : LocIndep k G) (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) {a : V} (ha : a ∈ attachPoints G C) (h2 : 2 ≤ (attachPoints G C).card)
    (hb : (attachPoints G C \ {a}).card ≤ m) : CloseToBipartite m G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mpr
    ⟨attachPoints G C \ {a}, hb, hitsOddCycles_erase_of_attachPoints_of_noCrossOver h hC hshort hnc ha
      h2⟩

/-- **THE OPTIMAL CONSTANT `1` AT `k = 1`: TWO ATTACHMENT POINTS AND NO CROSS-OVER.**  Since
`attachPoints G C ∖ {a}` is then the singleton `{b}`, one vertex suffices. -/
theorem closeToBipartite_one_of_noCrossOver_of_card_attachPoints_eq_two (hG : LocIndep 1 G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) {a : V} (ha : a ∈ attachPoints G C)
    (h2 : (attachPoints G C).card = 2) : CloseToBipartite 1 G := by
  refine closeToBipartite_of_noCrossOver hG (packingNumberOne_of_locIndep_one hG) hC hshort hnc ha
    (by omega) ?_
  have hcard1 : ({a} : Finset V) ∩ attachPoints G C = {a} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ ha⟩⟩
  have hcard : (attachPoints G C \ {a}).card = (attachPoints G C).card - 1 := by
    rw [Finset.card_sdiff, Finset.card_eq_one.mpr ⟨a, hcard1⟩]
  omega

/-- **THE OPTIMAL CONSTANT `2`, FOR EVERY `k`: THREE ATTACHMENT POINTS AND NO CROSS-OVER.**  The
certificate is the two attachment points other than `a`, and it lies on `C`. -/
theorem erdos73On_one_two_of_noCrossOver_of_card_attachPoints_le_three {k : ℕ} (hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hnc : NoCrossOver G C)
    {a : V} (ha : a ∈ attachPoints G C) (h3 : 3 ≤ (attachPoints G C).card)
    (hle : (attachPoints G C).card ≤ 3) : CloseToBipartite 2 G := by
  refine closeToBipartite_of_noCrossOver hG h hC hshort hnc ha (by omega) ?_
  have hcard1 : ({a} : Finset V) ∩ attachPoints G C = {a} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ ha⟩⟩
  have hcard : (attachPoints G C \ {a}).card = (attachPoints G C).card - 1 := by
    rw [Finset.card_sdiff, Finset.card_eq_one.mpr ⟨a, hcard1⟩]
  omega

/-- **ANY PAIR OF ATTACHMENT POINTS IS A CERTIFICATE WHEN THERE ARE EXACTLY THREE OF THEM AND NO
CROSS-OVER.**  The certificate lies on the shortest odd cycle `C`, not in its fan. -/
theorem hitsOddCycles_pair_of_noCrossOver_of_card_attachPoints_eq_three (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h3 : (attachPoints G C).card = 3)
    (hA : ({a, b, c} : Finset V) ⊆ attachPoints G C) : HitsOddCycles G ({a, b} : Finset V) := by
  have hcard3 : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hAc : attachPoints G C = ({a, b, c} : Finset V) := by
    have h := Finset.eq_of_subset_of_card_le (s := ({a, b, c} : Finset V))
      (t := attachPoints G C) hA (by rw [hcard3, h3])
    exact h.symm
  have heq : ({a, b} : Finset V) = attachPoints G C \ {c} := by
    rw [hAc]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hcA : c ∈ attachPoints G C := hA (by simp)
  rw [heq]
  exact hitsOddCycles_erase_of_attachPoints_of_noCrossOver h hC hshort hnc hcA (by omega)

/-- **A PAIR OF DISTINCT VERTICES HAS AT MOST TWO ELEMENTS.** -/
theorem card_le_two_pair {p q : V} (hne : p ≠ q) : ({p, q} : Finset V).card ≤ 2 := by
  have he : ({p, q} : Finset V) = insert p ({q} : Finset V) := rfl
  rw [he, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-! ## Part 5 — the tighter residual of the sharp case `k = 1` -/

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1`, WITH THE CERTIFICATE REQUIRED TO LIE IN THE ATTACHMENT
POINTS OF `C`.**

```lean
LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b}
```

This is *strictly weaker* than `JSP90.AttachThreeResidual` of round 136 — it only asks that some
2-transversal **on `C`** exists, while the latter allows it anywhere; the exhaustive search of
`discovery/JSP-000090/r137.c` (question `Q6`) shows that this is always enough. -/
def AttachThreeResidualRefined : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      3 ≤ (attachPoints G C).card → ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        HitsOddCycles G ({a, b} : Finset W)

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73, WITH THE CONSTANT `2`, FROM THE REFINED RESIDUAL.**
The four cases, exactly as in `JSP90.erdos73On_one_two_of_attachThreeResidual`. -/
theorem erdos73On_one_two_of_attachThreeResidualRefined (h : AttachThreeResidualRefined.{u}) :
    Erdős73On.{u} 1 2 := by
  intro W instW G hG
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
    by_cases hne : (boundary G C).Nonempty
    · by_cases hb : (attachPoints G C).card ≤ 2
      · exact ⟨attachPoints G C, hb,
          hitsOddCycles_attachPoints_of_packing_one (packingNumberOne_of_locIndep_one hG)
            hC hshort hne⟩
      · obtain ⟨a, b, hab, ha, hb, hh⟩ := h W instW G hG C hC hshort (by omega)
        exact ⟨{a, b}, card_le_two_pair hab, fun D hD => hh D hD⟩
    · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE REFINED RESIDUAL IS IMPLIED BY, AND IMPLIES, ROUND 136'S `AttachThreeResidual`.** -/
theorem attachThreeResidual_of_attachThreeResidualRefined (h : AttachThreeResidualRefined.{u}) :
    AttachThreeResidual.{u} := by
  intro W instW G hG C hC hshort h3
  obtain ⟨a, b, hab, ha, hb, hh⟩ := h W instW G hG C hC hshort h3
  exact ⟨{a, b}, card_le_two_pair hab, fun D hD => hh D hD⟩

/-! ## What is *not* proved

`JSP90.AttachThreeResidualRefined`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is not declared, so
the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`. -/

#print axioms JSP90.mem_attachPoints_exit
#print axioms JSP90.mem_attachPoints_entry
#print axioms JSP90.not_subset_of_isOddCycle_ne_of_shortest
#print axioms JSP90.exists_exit_of_mem_of_exists_not_mem
#print axioms JSP90.exists_entry_of_not_mem_of_exists_mem
#print axioms JSP90.two_le_card_of_mem_pair
#print axioms JSP90.exists_pair_ne_of_card_ge_two
#print axioms JSP90.two_le_card_attachPoints_inter_of_card_inter_ge_two
#print axioms JSP90.two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one
#print axioms JSP90.exists_mem_sdiff_singleton_of_card_ge_two
#print axioms JSP90.hitsOddCycles_erase_of_attachPoints_of_noCrossOver
#print axioms JSP90.closeToBipartite_of_noCrossOver
#print axioms JSP90.closeToBipartite_one_of_noCrossOver_of_card_attachPoints_eq_two
#print axioms JSP90.erdos73On_one_two_of_noCrossOver_of_card_attachPoints_le_three
#print axioms JSP90.hitsOddCycles_pair_of_noCrossOver_of_card_attachPoints_eq_three
#print axioms JSP90.erdos73On_one_two_of_attachThreeResidualRefined
#print axioms JSP90.attachThreeResidual_of_attachThreeResidualRefined

end Segment

end

end JSP90
