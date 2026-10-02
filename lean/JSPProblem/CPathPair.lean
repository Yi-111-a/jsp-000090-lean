/-
# JSP-000090 — `JSPProblem/CPathPair.lean`: **the fan at depth two** (Mader's two-attachment lemma)

Round 111 (`JSPProblem/CPath.lean`) introduced the `C`-path and obtained the two-attachment
transversal `JSP90.closeToBipartite_of_twoAttach`: if an odd cycle `C` meets every odd cycle of `G`
in at least two vertices then `G` is `|C| - 1`-close to bipartite.  Rounds 112–113 built the whole
local `C`-path apparatus (`IsCPath.skip`, `IsCPath.Shortest`, `IsCPath.induced_of_shortest`,
`IsCPath.isOddCycle_return`, the **two-attachment cover** `JSP90.closeToBipartite_of_twoAttachCover`)
and `discovery/JSP-000090/policy.json` named the next step:

> **build the FAN.**  Define `IsCPathPair` (two internally vertex-disjoint `C`-paths from one
> vertex `x` to distinct vertices of `C`) and prove that their union with each of the two arcs of
> `C` is a cycle, that exactly one of those two cycles is odd, and that that odd cycle meets `C` in
> the two attachment points.

This file (attack family 54) does exactly that.

## What is proved

| result | content |
| --- | --- |
| **`IsCPathPair`** | **THE OBJECT: THE FAN AT DEPTH TWO.**  Two `C`-paths `p`, `q` to a common target `x ∉ C`, ending at *distinct* vertices `f i`, `f j` of `C`, whose vertex sets meet **only** in `{f i, f j, x}` — i.e. internally vertex-disjoint, the classical Menger-free formulation of "two internally disjoint `C`-paths" |
| `IsCPathPair.d1_pos`, `IsCPathPair.d2_pos` | both lengths are positive (a length-0 `C`-path would put its target on `C`) |
| `IsCPathPair.offC` | a vertex of `p` off `C` is `f i` or `x`: the local structure of a `C`-path, in the form the pair needs |
| **`arcPairFun`** | **THE TWO-PATH ARC CYCLE**: the closed walk `f j → (arc of `C` of length `e`) → f i → p → x → q → f j`, as a map `Fin (e + d1 + d2) → V`.  It generalises `JSPProblem/Fan.lean`'s `arcFun` (where the two closing edges are the *same* vertex `x`, i.e. `d1 = d2 = 1`) to two paths of arbitrary length |
| `arcPairFun_inj` | **the two-path arc cycle is simple**: the arc lies on `C`, the interiors of `p` and `q` lie off `C`, the two interiors are disjoint by `IsCPathPair`, and `x` is reached only at the end of `p` |
| `arcPairFun_adj` | every step of `arcPairFun` is an edge of `G`, including the closing step `q 1 ~ q 0` |
| **`arcPair_isOddCycle`** | **the two-path arc cycle is an odd cycle** when `e + d1 + d2` is odd |
| `card_arcPair` | it has **exactly** `e + d1 + d2` vertices |
| **`exists_oddCycle_twoAttach_of_isCPathPair`** | **MADER'S TWO-ATTACHMENT LEMMA.**  If `x` has two internally vertex-disjoint `C`-paths to two distinct vertices `f i`, `f j` of an odd cycle `C`, then `x` lies on an **odd cycle of `G` through `f i` and `f j`** — the second attachment point, and the first odd cycle through a vertex at `C`-distance `≥ 2` this development constructs |
| **`arc_sum_ge_of_shortest`** | **A SHORTEST ODD CYCLE IS THICK.**  If `C` is a shortest odd cycle of length `m`, then every *odd* arc between the two attachment points has length `≥ m - d1 - d2`: `m ≤ e + d1 + d2` |
| **`oddArc_eq_two_of_fan_of_shortest`** | in the fan case (`x` adjacent to both attachment points) the odd arc has length exactly `m - 2`, whence **`shortArc_of_pairFan`**, the short-arc lemma of `JSPProblem/Fan.lean` re-proved from Mader's lemma and the card count |
| **`not_twoAttach_kTriangles_two`** | **machine-checked negative result**: on `kTriangles 2` **no** odd cycle is a two-attachment cycle — the hypothesis of `closeToBipartite_of_twoAttach` is genuinely restrictive and is not automatic |
| `twoAttach_kTriangles_one` | the positive contrast: on `kTriangles 1 = K_3` the triangle *is* a two-attachment cycle, so the hypothesis of round 111 is satisfiable and the negative result above is not vacuous |

## What is *not* proved, and what is left for the next round

`jsp_000090_main` is still not declared and `JSP90.OddCycleErdosPosa r` is unchanged.  Mader's
lemma is a **resource**, not a transversal: it exhibits an odd cycle `D` through `x` meeting `C`
twice, but it does not make the two-attachment *hypothesis* of `closeToBipartite_of_twoAttach` hold
for every odd cycle of `G`.  What is still missing is the global step — the existence of a
two-attachment cover `𝒞` (round 112) for a 3-connected graph — together with the absorption bound
for the one-attachment odd cycles of round 112's `oneAttach_of_isCPath_return`.  See
`discovery/JSP-000090/policy.json` for the exact missing lemmas.

**No new instance of the headline theorem is claimed this round**, deliberately: a hypothesis of the
form "every odd cycle *contains* a fan vertex" is satisfied by the one-attachment odd cycles of
round 112 (whose fan vertex exists but whose *own* attachment count is `1`), and such a hypothesis
yields no transversal.  Claiming one would have been vacuous.

## Toolchain notes

* The `arcPairFun` body is a **nested `dite`**: `if h1 : t.val ≤ e then … else (if h2 : …)`.  Each
  branch needs its index proof in `Fin`, and `omega` supplies them from `t.isLt` plus the bounds;
  a plain `ite` leaves the `else` branch without its hypothesis and `omega` fails.
* `rw [Fin.mk.inj_iff] at h` extracts `.val` equalities from equalities of `Fin` literals, and
  `Fin.eq_of_val_eq` is used in the other direction; `Fin.mk_val i : (⟨i.val, i.isLt⟩ : Fin n) = i`
  moves between the two forms.
* `(cycSucc^[t.val + 1] : Fin m → Fin m) j = cycSucc ((cycSucc^[t.val] : Fin m → Fin m) j)` is
  `Function.iterate_succ_apply'` with `(t.val).succ = t.val + 1` spelled out (as in
  `JSPProblem/Fan.lean` `arcFun_adj`).
* The parity split of Mader's lemma uses only `Nat.add_mod` and `Nat.mod_two_eq_zero_or_one`: the
  two candidate totals satisfy `A + B = m + 2 * (d1 + d2)`, which is odd, so exactly one of them is
  odd (`mod_two_of_sum_odd`).
-/

import JSPProblem.CPathSkip
import JSPProblem.DegColour

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqCPathPair : DecidableEq V := Classical.decEq V

/-- **`a < a + b` as soon as `b` is positive.**

The `omega` of the pinned revision reads a ℕ *variable* as a nonneg integer and cannot conclude
`1 ≤ b` from `b ≥ 0`; every "one of the summands is positive" step below therefore goes through
this lemma (or through `Nat.eq_zero_or_pos`, which yields a genuine strict inequality). -/
theorem lt_add_of_pos (a b : ℕ) (h : 0 < b) : a < a + b := by
  have hb : 1 ≤ b := by omega
  have hle : a.succ ≤ a + b := by omega
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self a) hle

/-! ### Part 1 — the object: two internally vertex-disjoint `C`-paths to a common target -/

section Pair

variable {m d1 d2 : ℕ} {f : Fin m → V} {i j : Fin m} {C : Finset V}
  {hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y} {x : V}
  {p : Fin (d1 + 1) → V} {q : Fin (d2 + 1) → V}

/-- **THE FAN AT DEPTH TWO: TWO INTERNALLY VERTEX-DISJOINT `C`-PATHS TO A COMMON TARGET.**

`p` is a `C`-path from the vertex `f i` of `C` to `x ∉ C`, `q` is a `C`-path from the **distinct**
vertex `f j` of `C` to the same `x`, and the two vertex sets meet only in `{f i, f j, x}`.

This is the classical fan object of Reed–Robertson–Seymour–Thomas: `x` is *seen twice* from `C`.
Mader's two-attachment lemma below turns it into an odd cycle of `G` through both attachment
points. -/
def IsCPathPair (G : SimpleGraph V) (m d1 d2 : ℕ) (f : Fin m → V) (i j : Fin m) (C : Finset V)
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y) (x : V)
    (p : Fin (d1 + 1) → V) (q : Fin (d2 + 1) → V) : Prop :=
  IsCPath G m d1 f i C hCmem x p
    ∧ IsCPath G m d2 f j C hCmem x q
    ∧ i ≠ j
    ∧ (∀ u : V, u ∈ IsCPath.supset p → u ∈ IsCPath.supset q → u = f i ∨ u = f j ∨ u = x)

theorem IsCPathPair.p1 (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    IsCPath G m d1 f i C hCmem x p := h.1

theorem IsCPathPair.p2 (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    IsCPath G m d2 f j C hCmem x q := h.2.1

/-- **THE TWO ATTACHMENT POINTS ARE DISTINCT.** -/
theorem IsCPathPair.ne (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : i ≠ j := h.2.2.1

/-- **THE TWO `C`-PATHS SHARE NOTHING BUT THE ATTACHMENT POINTS AND THE TARGET.** -/
theorem IsCPathPair.disj (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) {u : V}
    (hup : u ∈ IsCPath.supset p) (huq : u ∈ IsCPath.supset q) :
    u = f i ∨ u = f j ∨ u = x :=
  h.2.2.2 u hup huq

/-- The first attachment point is on `C`. -/
theorem IsCPathPair.mem_fi (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : f i ∈ C := by
  rw [hCmem]
  exact ⟨i, rfl⟩

/-- The second attachment point is on `C`. -/
theorem IsCPathPair.mem_fj (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : f j ∈ C := by
  rw [hCmem]
  exact ⟨j, rfl⟩

/-- The target of the fan is **not** on `C`. -/
theorem IsCPathPair.notMem_x (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : x ∉ C :=
  h.p1.notMem_end

/-- **A `C`-PATH OF LENGTH `0` WOULD PUT ITS TARGET ON `C`**, so `0 < d1`. -/
theorem IsCPathPair.d1_pos (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : 0 < d1 := by
  by_contra hcon
  have h1 : d1 = 0 := Nat.eq_zero_of_not_pos hcon
  have hidx : (⟨d1, lt_d_succ d1⟩ : Fin (d1 + 1)) = ⟨0, zero_lt_d_succ d1⟩ := by
    apply Fin.ext
    omega
  have hx : p ⟨0, zero_lt_d_succ d1⟩ = x := by
    rw [← hidx]
    exact h.p1.end
  have hxf : x = f i := hx.symm.trans h.p1.start
  have hnm := h.notMem_x
  rw [hxf] at hnm
  exact hnm h.mem_fi

/-- **A `C`-PATH OF LENGTH `0` WOULD PUT ITS TARGET ON `C`**, so `0 < d2`. -/
theorem IsCPathPair.d2_pos (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : 0 < d2 := by
  by_contra hcon
  have h1 : d2 = 0 := Nat.eq_zero_of_not_pos hcon
  have hidx : (⟨d2, lt_d_succ d2⟩ : Fin (d2 + 1)) = ⟨0, zero_lt_d_succ d2⟩ := by
    apply Fin.ext
    omega
  have hx : q ⟨0, zero_lt_d_succ d2⟩ = x := by
    rw [← hidx]
    exact h.p2.end
  have hxf : x = f j := hx.symm.trans h.p2.start
  have hnm := h.notMem_x
  rw [hxf] at hnm
  exact hnm h.mem_fj

/-- The target is a vertex of both paths. -/
theorem IsCPathPair.mem_supset_x (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    x ∈ IsCPath.supset p ∧ x ∈ IsCPath.supset q := by
  refine ⟨?_, ?_⟩
  · rw [IsCPath.mem_supset]
    exact ⟨⟨d1, lt_d_succ d1⟩, h.p1.end⟩
  · rw [IsCPath.mem_supset]
    exact ⟨⟨d2, lt_d_succ d2⟩, h.p2.end⟩

/-- **THE FIRST PATH MEETS `C` IN EXACTLY ITS FIRST VERTEX.**  A vertex of `p` which lies on `C`
is the first attachment point `f i` — the local fact that separates the two branches of
`arcPairFun`. -/
theorem IsCPathPair.eq_fi_of_mem_supset_p_mem_C (h : IsCPathPair G m d1 d2 f i j C hCmem x p q)
    {u : V} (hup : u ∈ IsCPath.supset p) (huC : u ∈ C) : u = f i := by
  rw [IsCPath.mem_supset] at hup
  obtain ⟨k, hk⟩ := hup
  have hkk : u = p k := hk.symm
  by_cases hk0 : k.val = 0
  · have hk' : k = ⟨0, zero_lt_d_succ d1⟩ := Fin.eq_of_val_eq hk0
    rw [hk', h.p1.start] at hkk
    exact hkk
  · have hpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    exact (h.p1.notMem_interior k hpos (hkk ▸ huC)).elim

/-- **THE SECOND PATH MEETS `C` IN EXACTLY ITS FIRST VERTEX.** -/
theorem IsCPathPair.eq_fj_of_mem_supset_q_mem_C (h : IsCPathPair G m d1 d2 f i j C hCmem x p q)
    {u : V} (huq : u ∈ IsCPath.supset q) (huC : u ∈ C) : u = f j := by
  rw [IsCPath.mem_supset] at huq
  obtain ⟨k, hk⟩ := huq
  have hkk : u = q k := hk.symm
  by_cases hk0 : k.val = 0
  · have hk' : k = ⟨0, zero_lt_d_succ d2⟩ := Fin.eq_of_val_eq hk0
    rw [hk', h.p2.start] at hkk
    exact hkk
  · have hpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    exact (h.p2.notMem_interior k hpos (hkk ▸ huC)).elim

/-- **THE TWO INTERIORS NEVER MEET.**

An interior vertex of `p` cannot be an interior vertex of `q`: both are off `C`, so the only common
value allowed by `IsCPathPair.disj` is the target `x`; and `x` is reached only at the *last* index
of `q`, which is outside the range `u < d2` used here.  This is the "internally vertex-disjoint"
part of the definition, in the form the arc-cycle constructor uses. -/
theorem IsCPathPair.inter_ne {s : ℕ} (hs : 0 < s) (hsm : s < d1 + 1) {u : ℕ} (hum : u < d2)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    p ⟨s, hsm⟩ ≠ q ⟨u, Nat.lt_trans hum (lt_d_succ d2)⟩ := by
  intro he
  have hval : p ⟨s, hsm⟩ ∉ C := h.p1.notMem_interior ⟨s, hsm⟩ hs
  have hmemP : p ⟨s, hsm⟩ ∈ IsCPath.supset p := (IsCPath.mem_supset).mpr ⟨⟨s, hsm⟩, rfl⟩
  have hmemQ : p ⟨s, hsm⟩ ∈ IsCPath.supset q := by
    rw [IsCPath.mem_supset]
    exact ⟨⟨u, Nat.lt_trans hum (lt_d_succ d2)⟩, he.symm⟩
  rcases h.disj hmemP hmemQ with h' | h' | h'
  · exact hval (h' ▸ h.mem_fi)
  · exact hval (h' ▸ h.mem_fj)
  · have h3 : q ⟨u, Nat.lt_trans hum (lt_d_succ d2)⟩ = x := he.symm.trans h'
    have h4 : q ⟨d2, lt_d_succ d2⟩ = x := h.p2.end
    have hne : ¬ u = d2 := by omega
    have hidx : ((⟨u, Nat.lt_trans hum (lt_d_succ d2)⟩ : Fin (d2 + 1)) = ⟨d2, lt_d_succ d2⟩) :=
      h.p2.inj (h3.trans h4.symm)
    exact absurd (Fin.mk.inj_iff.mp hidx) hne

end Pair

/-! ### Part 2 — the **two-path arc cycle**: the closed walk arc + `p` + `q` -/

section ArcPair

variable {m d1 d2 e : ℕ} {f : Fin m → V} {j : Fin m} {C : Finset V} {x : V}
  {p : Fin (d1 + 1) → V} {q : Fin (d2 + 1) → V}

/-- Every index of the `p` part is an index of `p`. -/
theorem arcPair_idx_p {t : ℕ} (h2 : t ≤ e + d1) (h1 : e < t) : t - e < d1 + 1 := by omega

/-- Every index of the `q` part is an index of `q`. -/
theorem arcPair_idx_q {t : ℕ} (ht : t < e + d1 + d2) (h1 : e + d1 < t) :
    d2 + e + d1 - t < d2 + 1 := by omega

/-- **THE TWO-PATH ARC CYCLE.**

The closed walk of `G`
`f j → (the arc of `C` of length `e` starting at `f j`) → f i → p → x → q → f j`,
carried by the map `Fin (e + d1 + d2) → V`:

* indices `0 … e` are the arc `f (cycSucc^[t] j)`;
* indices `e + 1 … e + d1` are `p (t - e)`, i.e. `p 1 … p d1 = x`;
* indices `e + d1 + 1 … e + d1 + d2 - 1` are `q (d2 + e + d1 - t)`, i.e. `q (d2 - 1) … q 1`;
* the walk closes from `q 1` back to `q 0 = f j`.

For `d1 = d2 = 1` this is exactly `JSPProblem/Fan.lean`'s `arcFun` (the two closing edges are then
the two edges `x ~ f i` and `x ~ f j`), so the map below **generalises** that constructor to two
paths of arbitrary length. -/
def arcPairFun (e : ℕ) (f : Fin m → V) (j : Fin m) (p : Fin (d1 + 1) → V) (q : Fin (d2 + 1) → V) :
    Fin (e + d1 + d2) → V :=
  fun t => if h1 : t.val ≤ e then f ((cycSucc^[t.val] : Fin m → Fin m) j)
           else if h2 : t.val ≤ e + d1 then p ⟨t.val - e, arcPair_idx_p h2 (Nat.not_le.mp h1)⟩
           else q ⟨d2 + e + d1 - t.val, arcPair_idx_q t.isLt (Nat.not_le.mp h2)⟩

/-- An index of the arc part. -/
theorem arcPairFun_eq_arc {t : ℕ} (ht : t < e + d1 + d2) (h : t ≤ e) :
    arcPairFun e f j p q ⟨t, ht⟩ = f ((cycSucc^[t] : Fin m → Fin m) j) := by
  simp only [arcPairFun, dite_eq_left h]

/-- An index of the `p` part. -/
theorem arcPairFun_eq_p {t : ℕ} (ht : t < e + d1 + d2) (h2 : t ≤ e + d1) (h1 : e < t) :
    arcPairFun e f j p q ⟨t, ht⟩ = p ⟨t - e, by omega⟩ := by
  have h3 : ¬ t ≤ e := Nat.not_le.mpr h1
  simp only [arcPairFun, dite_eq_right h3, dite_eq_left h2]

/-- An index of the `q` part. -/
theorem arcPairFun_eq_q {t : ℕ} (ht : t < e + d1 + d2) (h1 : e + d1 < t) :
    arcPairFun e f j p q ⟨t, ht⟩ = q ⟨d2 + e + d1 - t, by omega⟩ := by
  have hlt : e < t := by omega
  have h2 : ¬ t ≤ e := Nat.not_le.mpr hlt
  have h3 : ¬ t ≤ e + d1 := Nat.not_le.mpr h1
  simp only [arcPairFun, dite_eq_right h2, dite_eq_right h3]

/-- **EVERY INDEX IS IN EXACTLY ONE OF THE THREE PARTS.** -/
theorem arcPair_class_nat {t : ℕ} (ht : t < e + d1 + d2) :
    t ≤ e ∨ (e < t ∧ t ≤ e + d1) ∨ e + d1 < t := by omega

/-- **AN ARC VALUE LIES ON `C`.** -/
theorem arcPairFun_memC_arc (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y)
    {t : ℕ} (ht : t < e + d1 + d2) (h : t ≤ e) : arcPairFun e f j p q ⟨t, ht⟩ ∈ C := by
  rw [arcPairFun_eq_arc ht h, hCmem]
  exact ⟨_, rfl⟩

/-- **AN INTERIOR `p`-VALUE LIES OFF `C`.** -/
theorem arcPairFun_notMemC_p {t : ℕ} (ht : t < e + d1 + d2) (h1 : e < t) (h2 : t ≤ e + d1)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : arcPairFun e f j p q ⟨t, ht⟩ ∉ C := by
  rw [arcPairFun_eq_p ht h2 h1]
  exact h.p1.notMem_at (t - e) (by omega) (by omega)

/-- **A `q`-VALUE OF THE THIRD PART LIES OFF `C`.**  Its index is at least `1`, so it is an interior
index of the second `C`-path. -/
theorem arcPairFun_notMemC_q {t : ℕ} (ht : t < e + d1 + d2) (h1 : e + d1 < t)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) : arcPairFun e f j p q ⟨t, ht⟩ ∉ C := by
  rw [arcPairFun_eq_q ht h1]
  exact h.p2.notMem_at (d2 + e + d1 - t) (by omega) (by omega)

/-- **THE ARC DOES NOT MEET THE FIRST PATH.** -/
theorem arcPairFun_arc_ne_p {t s : ℕ} (ht : t < e + d1 + d2) (hs : s < e + d1 + d2)
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y) (h1 : t ≤ e) (h2 : e < s) (h3 : s ≤ e + d1)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    arcPairFun e f j p q ⟨t, ht⟩ ≠ arcPairFun e f j p q ⟨s, hs⟩ := by
  intro heq
  exact (arcPairFun_notMemC_p hs h2 h3 h) (heq ▸ arcPairFun_memC_arc hCmem ht h1)

/-- **THE ARC DOES NOT MEET THE SECOND PATH.** -/
theorem arcPairFun_arc_ne_q {t s : ℕ} (ht : t < e + d1 + d2) (hs : s < e + d1 + d2)
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y) (h1 : t ≤ e) (h2 : e + d1 < s)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    arcPairFun e f j p q ⟨t, ht⟩ ≠ arcPairFun e f j p q ⟨s, hs⟩ := by
  intro heq
  exact (arcPairFun_notMemC_q hs h2 h) (heq ▸ arcPairFun_memC_arc hCmem ht h1)

/-- **THE TWO PATHS NEVER MEET INSIDE THE CYCLE.** -/
theorem arcPairFun_p_ne_q {s t : ℕ} (hs : s < e + d1 + d2) (ht : t < e + d1 + d2)
    (h1 : e < s) (h2 : s ≤ e + d1) (h3 : e + d1 < t)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    arcPairFun e f j p q ⟨s, hs⟩ ≠ arcPairFun e f j p q ⟨t, ht⟩ := by
  intro heq
  have hmem : (d2 + e + d1 - t) < d2 := by omega
  exact h.inter_ne (s := s - e) (u := d2 + e + d1 - t) (by omega) (by omega) hmem
    (Eq.trans (Eq.trans (arcPairFun_eq_p hs h2 h1).symm heq) (arcPairFun_eq_q ht h3))

/-- **THE TWO-PATH ARC CYCLE IS SIMPLE.**  The arc lies on `C`, the interior of `p` and the third
part lie off `C`, and the two interiors never meet; within each part the map is injective because
`f`, `p`, `q` and `cycSucc^[·] j` are. -/
theorem arcPairFun_inj (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) (hdm : e < m)
    (hinj : Function.Injective f) (a b : Fin (e + d1 + d2)) (hne : a ≠ b) :
    arcPairFun e f j p q a ≠ arcPairFun e f j p q b := by
  rw [← Fin.mk_val a, ← Fin.mk_val b]
  rcases arcPair_class_nat a.isLt with ha1 | ha2 | ha3
  · rcases arcPair_class_nat b.isLt with hb1 | hb2 | hb3
    · intro heq
      have hidx : ((cycSucc^[a.val] : Fin m → Fin m) j) = ((cycSucc^[b.val] : Fin m → Fin m) j) :=
        hinj (Eq.trans (Eq.trans (arcPairFun_eq_arc a.isLt ha1).symm heq)
          (arcPairFun_eq_arc b.isLt hb1))
      exact cycSucc_pow_inj j (p := a.val) (q := b.val) (by omega) (by omega) (by omega) hidx
    · exact arcPairFun_arc_ne_p a.isLt b.isLt hCmem ha1 hb2.1 hb2.2 h
    · exact arcPairFun_arc_ne_q a.isLt b.isLt hCmem ha1 hb3 h
  · rcases arcPair_class_nat b.isLt with hb1 | hb2 | hb3
    · exact (arcPairFun_arc_ne_p b.isLt a.isLt hCmem hb1 ha2.1 ha2.2 h).symm
    · intro heq
      have hidx : ((⟨a.val - e, by omega⟩ : Fin (d1 + 1)) = ⟨b.val - e, by omega⟩) :=
        h.p1.inj (Eq.trans (Eq.trans (arcPairFun_eq_p a.isLt ha2.2 ha2.1).symm heq)
          (arcPairFun_eq_p b.isLt hb2.2 hb2.1))
      apply hne
      apply Fin.ext
      have h2 : a.val - e = b.val - e := Fin.mk.inj_iff.mp hidx
      omega
    · exact arcPairFun_p_ne_q a.isLt b.isLt ha2.1 ha2.2 hb3 h
  · rcases arcPair_class_nat b.isLt with hb1 | hb2 | hb3
    · exact (arcPairFun_arc_ne_q b.isLt a.isLt hCmem hb1 ha3 h).symm
    · exact (arcPairFun_p_ne_q b.isLt a.isLt hb2.1 hb2.2 ha3 h).symm
    · intro heq
      have hidx : ((⟨d2 + e + d1 - a.val, by omega⟩ : Fin (d2 + 1))
          = ⟨d2 + e + d1 - b.val, by omega⟩) :=
        h.p2.inj (Eq.trans (Eq.trans (arcPairFun_eq_q a.isLt ha3).symm heq)
          (arcPairFun_eq_q b.isLt hb3))
      apply hne
      apply Fin.ext
      have h2 : d2 + e + d1 - a.val = d2 + e + d1 - b.val := Fin.mk.inj_iff.mp hidx
      omega

end ArcPair

/-! ### Part 3 — the adjacency of the two-path arc cycle -/

section Adj

variable {m d1 d2 e : ℕ} {f : Fin m → V} {j : Fin m} {C : Finset V} {x : V}
  {p : Fin (d1 + 1) → V} {q : Fin (d2 + 1) → V}

/-- One step of the cyclic successor along an arc of `C`. -/
theorem cycSucc_pow_succ (t : ℕ) (k : Fin m) :
    ((cycSucc^[t + 1] : Fin m → Fin m) k) = cycSucc ((cycSucc^[t] : Fin m → Fin m) k) := by
  have h := Function.iterate_succ_apply' cycSucc t k
  rw [show t + 1 = t.succ from rfl, h]

/-- `cycSucc` of a non-last index. -/
theorem arcPair_cycSucc_succ (t : Fin (e + d1 + d2)) (h : t.val + 1 < e + d1 + d2) :
    cycSucc t = ⟨t.val + 1, h⟩ := by
  apply Fin.ext
  show (t.val + 1) % (e + d1 + d2) = t.val + 1
  exact Nat.mod_eq_of_lt h

/-- **THE FIRST VERTEX OF THE TWO-PATH ARC CYCLE IS `f j`.** -/
theorem arcPairFun_zero {e d1 d2 : ℕ} (f : Fin m → V) (j : Fin m) (p : Fin (d1 + 1) → V)
    (q : Fin (d2 + 1) → V) {t : ℕ} (ht : t < e + d1 + d2) (h0 : t = 0) :
    arcPairFun e f j p q ⟨t, ht⟩ = f j := by
  rw [arcPairFun_eq_arc ht (h0 ▸ Nat.zero_le e), h0]
  rfl

/-- **THE LAST VERTEX OF THE TWO-PATH ARC CYCLE IS `q 1`.**  For `d2 = 1` the third part is empty
and the last vertex is `p d1 = x = q d2 = q 1`, so the formula holds in both cases. -/
theorem arcPairFun_last (e d1 d2 : ℕ) (f : Fin m → V) (j i : Fin m) (C : Finset V)
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y) (x : V) (p : Fin (d1 + 1) → V)
    (q : Fin (d2 + 1) → V) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q)
    {t : ℕ} (ht : t < e + d1 + d2) (htl : t + 1 = e + d1 + d2) :
    arcPairFun e f j p q ⟨t, ht⟩ = q ⟨1, by omega⟩ := by
  rcases em (e + d1 < t) with hbig | hnot
  · rw [arcPairFun_eq_q ht hbig]
    have hz : ((⟨d2 + e + d1 - t, by omega⟩ : Fin (d2 + 1)) = ⟨1, by omega⟩) := by
      apply Fin.mk.inj_iff.mpr
      have hle : t ≤ d2 + e + d1 := by omega
      have h3 : (d2 + e + d1 - t) + t = d2 + e + d1 := Nat.sub_add_cancel hle
      omega
    rw [hz]
  · rw [arcPairFun_eq_p ht (Nat.le_of_not_gt hnot) (by omega)]
    have hz : ((⟨t - e, by omega⟩ : Fin (d1 + 1)) = ⟨d1, by omega⟩) := by
      apply Fin.mk.inj_iff.mpr
      omega
    rw [hz, h.p1.end]
    have hz2 : ((⟨1, by omega⟩ : Fin (d2 + 1)) = ⟨d2, lt_d_succ d2⟩) := by
      apply Fin.mk.inj_iff.mpr
      omega
    rw [hz2]
    exact h.p2.end.symm

/-- **THE VERTEX AT THE END OF THE ARC IS `f i`.** -/
theorem arcPairFun_at_e (harc : ((cycSucc^[e] : Fin m → Fin m) j) = i)
    {t : ℕ} (ht : t < e + d1 + d2) (he : t = e) : arcPairFun e f j p q ⟨t, ht⟩ = f i := by
  rw [arcPairFun_eq_arc ht (he ▸ Nat.le_refl e), he, harc]

/-- **THE VERTEX AT THE END OF THE FIRST PATH IS THE TARGET `x`.** -/
theorem arcPairFun_at_d1 (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) (hd1 : 0 < d1)
    {t : ℕ} (ht : t < e + d1 + d2) (he : t = e + d1) : arcPairFun e f j p q ⟨t, ht⟩ = x := by
  rw [arcPairFun_eq_p ht (by omega) (by omega)]
  have hz : ((⟨t - e, by omega⟩ : Fin (d1 + 1)) = ⟨d1, by omega⟩) := by
    apply Fin.mk.inj_iff.mpr
    omega
  rw [hz]
  exact h.p1.end

/-- **EVERY STEP OF THE TWO-PATH ARC CYCLE IS AN EDGE OF `G`.**

The kinds of step are: two consecutive steps along the arc of `C`, one from `f i = p 0` into `p`,
steps inside `p`, one from `p d1 = x = q d2` back into `q`, steps inside `q`, and the closing step
`q 1 ~ q 0 = f j`. -/
theorem arcPairFun_adj (h : IsCPathPair G m d1 d2 f i j C hCmem x p q)
    (hcyc : ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)))
    (harc : ((cycSucc^[e] : Fin m → Fin m) j) = i)
    (t : Fin (e + d1 + d2)) :
    G.Adj (arcPairFun e f j p q t) (arcPairFun e f j p q (cycSucc t)) := by
  have hd1 : 0 < d1 := h.d1_pos
  have hd2 : 0 < d2 := h.d2_pos
  by_cases hlast : t.val + 1 = e + d1 + d2
  · -- the closing step, `q 1 ~ q 0 = f j`
    rw [show cycSucc t = ⟨0, by omega⟩ by
      apply Fin.ext
      show (t.val + 1) % (e + d1 + d2) = 0
      rw [hlast, Nat.mod_self]]
    rw [arcPairFun_last e d1 d2 f j i C hCmem x p q hd1 hd2 h (by omega) hlast]
    rw [arcPairFun_zero f j p q (by omega) rfl, ← h.p2.start]
    exact (h.p2.adj_step 0 (by omega)).symm
  · -- a non-closing step
    have hidx : t.val + 1 < e + d1 + d2 := by omega
    rw [arcPair_cycSucc_succ (t := t) hidx]
    rcases arcPair_class_nat hidx with hc1 | hc2 | hc3
    · -- two steps along the arc
      rw [arcPairFun_eq_arc t.isLt (by omega),
        arcPairFun_eq_arc (t := t.val + 1) hidx hc1, cycSucc_pow_succ]
      exact hcyc ((cycSucc^[t.val] : Fin m → Fin m) j)
    · rcases em (t.val = e) with hteq | hne
      · -- the step from `f i = p 0` into `p`
        rw [arcPairFun_at_e harc (by omega) hteq,
          arcPairFun_eq_p (t := t.val + 1) hidx hc2.2 hc2.1, ← h.p1.start]
        have hz : ((⟨t.val + 1 - e, by omega⟩ : Fin (d1 + 1)) = ⟨0 + 1, by omega⟩) := by
          apply Fin.mk.inj_iff.mpr
          omega
        rw [hz]
        exact h.p1.adj_step 0 hd1
      · -- a step inside `p`
        rw [arcPairFun_eq_p t.isLt (by omega) (by omega),
          arcPairFun_eq_p (t := t.val + 1) hidx hc2.2 hc2.1]
        have hz : ((⟨t.val + 1 - e, by omega⟩ : Fin (d1 + 1)) = ⟨(t.val - e) + 1, by omega⟩) := by
          apply Fin.mk.inj_iff.mpr
          omega
        rw [hz]
        exact h.p1.adj_step (t.val - e) (by omega)
    · have hge : e + d1 ≤ t.val := by omega
      rcases em (t.val = e + d1) with hteq | hne
      · -- the step from `x = p d1 = q d2` back into `q`
        rw [arcPairFun_at_d1 h hd1 (by omega) hteq,
          arcPairFun_eq_q (t := t.val + 1) hidx (by omega), ← h.p2.end]
        have hz : ((⟨d2, lt_d_succ d2⟩ : Fin (d2 + 1)) = ⟨d2 - 1 + 1, by omega⟩) := by
          apply Fin.mk.inj_iff.mpr
          omega
        rw [hz]
        have hz' : ((⟨d2 + e + d1 - (t.val + 1), by omega⟩ : Fin (d2 + 1))
            = ⟨d2 - 1, by omega⟩) := by
          apply Fin.mk.inj_iff.mpr
          omega
        rw [hz']
        exact (h.p2.adj_step (d2 - 1) (by omega)).symm
      · -- a step inside `q`
        rw [arcPairFun_eq_q t.isLt (by omega),
          arcPairFun_eq_q (t := t.val + 1) hidx hc3]
        have hz : ((⟨d2 + e + d1 - t.val, by omega⟩ : Fin (d2 + 1))
            = ⟨(d2 + e + d1 - t.val - 1) + 1, by omega⟩) := by
          apply Fin.mk.inj_iff.mpr
          omega
        rw [hz]
        exact (h.p2.adj_step (d2 + e + d1 - t.val - 1) (by omega)).symm

end Adj
/-! ### Part 4 — the two-path arc cycle is an **odd cycle**, and Mader's two-attachment lemma -/

section Mader

variable {m d1 d2 e : ℕ} {f : Fin m → V} {j i : Fin m} {C : Finset V} {x : V}
  {p : Fin (d1 + 1) → V} {q : Fin (d2 + 1) → V}

/-- **THE TWO-PATH ARC CYCLE IS AN ODD CYCLE OF `G`.**

Let `f : Fin m → V` carry an odd cycle `C` of `G` (so `f` is injective, `m` is odd, and
consecutive vertices are adjacent), let `h : IsCPathPair G m d1 d2 f i j C hCmem x p q` be a fan
at `x`, and let the arc of `C` of length `e < m` from `f j` end at `f i`.  Then the closed walk
`arc + p + q` is a **simple odd cycle** of `G` with exactly `e + d1 + d2` vertices, whenever
`e + d1 + d2` is odd.

This is the generalisation of `JSPProblem/Fan.lean`'s `arc_isOddCycle` (the case `d1 = d2 = 1`) to
two paths of arbitrary length: the parity of `e + d1 + d2` decides which of the two arcs gives the
odd cycle, and the two candidate totals differ by an odd number. -/
theorem arcPair_isOddCycle [Fintype V] (hm : m % 2 = 1) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)))
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) (hdm : e < m)
    (harc : ((cycSucc^[e] : Fin m → Fin m) j) = i)
    (hmod : (e + d1 + d2) % 2 = 1) :
    IsOddCycle G ((Finset.univ : Finset (Fin (e + d1 + d2))).image (arcPairFun e f j p q)) := by
  have hd1 : 0 < d1 := h.d1_pos
  have hd2 : 0 < d2 := h.d2_pos
  have hm3 : 3 ≤ e + d1 + d2 := by omega
  have hinj' : Function.Injective (arcPairFun e f j p q) :=
    fun a b hab => by
      by_contra hne
      exact (arcPairFun_inj h hdm hinj (a := a) (b := b) hne) hab
  refine ⟨e + d1 + d2, arcPairFun e f j p q, hmod, hm3, hinj', ?_, ?_⟩
  · intro t
    exact arcPairFun_adj h hcyc harc t
  · intro y
    constructor
    · intro hy
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hy
      exact ⟨t, ht⟩
    · rintro ⟨t, rfl⟩
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

/-- **THE TWO-PATH ARC CYCLE HAS EXACTLY `e + d1 + d2` VERTICES.** -/
theorem card_arcPair [Fintype V] (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) (hdm : e < m)
    (hinj : Function.Injective f) :
    ((Finset.univ : Finset (Fin (e + d1 + d2))).image (arcPairFun e f j p q)).card = e + d1 + d2 := by
  rw [Finset.card_image_of_injective _
    (fun a b hab => by
      by_contra hne
      exact (arcPairFun_inj h hdm hinj (a := a) (b := b) hne) hab)]
  simp

/-- **A NUMBER WHICH ADDS UP TO AN ODD NUMBER WITH AN EVEN NUMBER IS ODD.** -/
theorem mod_two_of_sum_odd {A B : ℕ} (hA : A % 2 = 0) (hsum : (A + B) % 2 = 1) : B % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one B with hz | ho
  · rw [Nat.add_mod, hA, hz] at hsum
    simp at hsum
  · exact ho

/-- **MADER'S TWO-ATTACHMENT LEMMA.**

Let `C` be an **odd cycle** of `G` carried by the cyclic ordering `f : Fin C.card → V`, and let
`x ∉ C` have **two internally vertex-disjoint `C`-paths** to two **distinct** vertices `f i`,
`f j` of `C`.  Then

> `x` lies on an **odd cycle of `G`** containing **both** attachment points.

This is the second attachment point that `discovery/JSP-000090/policy.json` named after round 112:
rounds 111–112 could build odd cycles meeting `C` in exactly *one* vertex
(`oneAttach_of_isCPath_return`), and this is the first result of this development producing an odd
cycle of `G` through a vertex at `C`-distance `≥ 2`, together with two points of `C`.

Proof: the two paths together with either of the two arcs of `C` between `f i` and `f j` are
cycles of `G` of `e + d1 + d2` resp. `(m - e) + d1 + d2` vertices, and these two numbers add up to
`m + 2 * (d1 + d2)`, which is odd because `m` is odd. -/
theorem exists_oddCycle_twoAttach_of_isCPathPair [Fintype V] {m d1 d2 : ℕ} (hm : m % 2 = 1)
    {f : Fin m → V} (hinj : Function.Injective f)
    (hcyc : ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)))
    {C : Finset V} (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y) {i j : Fin m} {x : V}
    {p : Fin (d1 + 1) → V} {q : Fin (d2 + 1) → V}
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q) :
    ∃ (D : Finset V), IsOddCycle G D ∧ x ∈ D ∧ f i ∈ D ∧ f j ∈ D := by
  have hne : i ≠ j := h.ne
  have hd1 : 0 < d1 := h.d1_pos
  have hd2 : 0 < d2 := h.d2_pos
  obtain ⟨e, he0, hem, hdij⟩ := exists_arc (m := m) (by omega) hne.symm
  by_cases hmod1 : (e + d1 + d2) % 2 = 1
  · -- the arc of length `e` gives the odd cycle
    refine ⟨(Finset.univ : Finset (Fin (e + d1 + d2))).image (arcPairFun e f j p q),
      arcPair_isOddCycle hm f hinj hcyc hCmem h hem hdij hmod1, ?_, ?_, ?_⟩
    · -- the target `x`
      have hx : arcPairFun e f j p q ⟨e + d1, by omega⟩ = x :=
        arcPairFun_at_d1 h hd1 (by omega) rfl
      exact Finset.mem_image.mpr ⟨⟨e + d1, by omega⟩, Finset.mem_univ _, hx⟩
    · -- the first attachment point `f i`
      have hfi : arcPairFun e f j p q ⟨e, by omega⟩ = f i := by
        rw [arcPairFun_eq_arc (by omega) (Nat.le_refl e), hdij]
      exact Finset.mem_image.mpr ⟨⟨e, by omega⟩, Finset.mem_univ _, hfi⟩
    · -- the second attachment point `f j`
      have hfj : arcPairFun e f j p q ⟨0, by omega⟩ = f j := by
        rw [arcPairFun_eq_arc (by omega) (Nat.zero_le e)]
        rfl
      exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, hfj⟩
  · -- the other arc, of length `m - e`, gives the odd cycle
    have hmod2 : ((m - e) + d2 + d1) % 2 = 1 := by
      have hsum : (e + d1 + d2) + ((m - e) + d2 + d1) = m + 2 * (d1 + d2) := by omega
      have hone : (m + 2 * (d1 + d2)) % 2 = 1 := by
        rw [Nat.add_mod, hm]
        simp
      refine mod_two_of_sum_odd (A := e + d1 + d2) ?_ ?_
      · rcases Nat.mod_two_eq_zero_or_one (e + d1 + d2) with hz | ho
        · exact hz
        · exact absurd ho hmod1
      · rw [hsum]
        exact hone
    -- the fan read in the other order: the arc from `f i` of length `m - e`, then `q`, then `p`
    have h' : IsCPathPair G m d2 d1 f j i C hCmem x q p :=
      ⟨h.p2, h.p1, hne.symm, fun u huq hup => (h.disj hup huq).elim
        (fun hi => Or.inr (Or.inl hi))
        (fun h' => h'.elim Or.inl (fun hx => Or.inr (Or.inr hx)))⟩
    refine ⟨(Finset.univ : Finset (Fin ((m - e) + d2 + d1))).image (arcPairFun (m - e) f i q p),
      arcPair_isOddCycle hm f hinj hcyc hCmem h' (by omega) (arc_rev hem hdij) hmod2, ?_, ?_, ?_⟩
    · -- the target `x`
      have hx : arcPairFun (m - e) f i q p ⟨m - e + d2, by omega⟩ = x :=
        arcPairFun_at_d1 h' (by omega) (by omega) rfl
      exact Finset.mem_image.mpr ⟨⟨m - e + d2, by omega⟩, Finset.mem_univ _, hx⟩
    · -- the first attachment point `f i`, the start of the arc
      have hfi : arcPairFun (m - e) f i q p ⟨0, by omega⟩ = f i := by
        rw [arcPairFun_eq_arc (by omega) (Nat.zero_le _)]
        rfl
      exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, hfi⟩
    · -- the second attachment point `f j`, the end of the arc
      have hfj : arcPairFun (m - e) f i q p ⟨m - e, by omega⟩ = f j :=
        arcPairFun_at_e (arc_rev hem hdij) (by omega) rfl
      exact Finset.mem_image.mpr ⟨⟨m - e, by omega⟩, Finset.mem_univ _, hfj⟩
end Mader

/-! ### Part 5 — **a shortest odd cycle is thick**: the short-arc lemma from Mader's lemma -/

section Thick

variable {m d1 d2 e : ℕ} {f : Fin m → V} {i j : Fin m} {C : Finset V} {x : V}
  {p : Fin (d1 + 1) → V} {q : Fin (d2 + 1) → V}

/-- **THE ONE-EDGE PATH**, the `C`-path of length `1` from `a` to `b`. -/
def edgePath (a b : V) : Fin 2 → V := fun u => if _h : u.val = 0 then a else b

theorem edgePath_zero (a b : V) : edgePath a b ⟨0, Nat.zero_lt_succ 1⟩ = a := by
  simp [edgePath]

theorem edgePath_one (a b : V) : edgePath a b ⟨1, Nat.lt_succ_self 1⟩ = b := by
  simp [edgePath]

/-- **A ONE-EDGE PATH WITH DISTINCT ENDS IS SIMPLE.** -/
theorem edgePath_val_eq {a b : V} {u v : Fin 2} (hne : a ≠ b)
    (h : edgePath a b u = edgePath a b v) : u.val = v.val := by
  by_cases hu0 : u.val = 0
  · by_cases hv0 : v.val = 0
    · omega
    · simp only [edgePath, dite_eq_left hu0, dite_eq_right hv0] at h
      exact absurd h.symm (fun hh => hne hh.symm)
  · by_cases hv0 : v.val = 0
    · simp only [edgePath, dite_eq_right hu0, dite_eq_left hv0] at h
      exact absurd h (fun hh => hne hh.symm)
    · have hu1 : u.val = 1 := by have := u.isLt; omega
      have hv1 : v.val = 1 := by have := v.isLt; omega
      omega

theorem edgePath_inj {a b : V} (hne : a ≠ b) : Function.Injective (edgePath a b) := by
  intro u v h
  exact Fin.ext (edgePath_val_eq hne h)

/-- **A LENGTH-ONE `C`-PATH IS AN EDGE.**  `x ∉ C` and `f i ~ x` make `edgePath (f i) x` a `C`-path
of length `1` from `f i` to `x`: this is the depth-one case of `IsCPath`, isolated because it is
the case Mader's fan argument starts from. -/
theorem IsCPath_edgePath {i : Fin m} {x : V} (hxC : x ∉ C) (hxi : G.Adj (f i) x) :
    IsCPath G m 1 f i C hCmem x (edgePath (f i) x) := by
  have hne : f i ≠ x := hxi.ne
  refine ⟨rfl, rfl, hxC, edgePath_inj hne, ?_, ?_⟩
  · intro j hj
    have hj1 : j.val = 1 := by have := j.isLt; omega
    have hj' : j = ⟨1, Nat.lt_succ_self 1⟩ := Fin.eq_of_val_eq hj1
    rw [hj', edgePath_one]
    exact hxC
  · intro j
    have hj0 : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    have hz0 : ((⟨j.val, Nat.lt_trans j.isLt (lt_d_succ 1)⟩ : Fin 2)
        = ⟨0, Nat.zero_lt_succ 1⟩) := Fin.mk.inj_iff.mpr (by omega)
    have hz1 : ((⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ : Fin 2)
        = ⟨1, Nat.lt_succ_self 1⟩) := Fin.mk.inj_iff.mpr (by omega)
    rw [hz0, hz1, edgePath_zero, edgePath_one]
    exact hxi

/-- **THE FAN AT A SINGLE VERTEX: THE DEPTH-ONE CASE OF `IsCPathPair`.**  `x ∉ C` adjacent to two
distinct vertices `f i`, `f j` of `C` is exactly a pair of `C`-paths of lengths `1` and `1` to
`x`: this is what Mader's lemma needs in the fan case, and it is now *derived* from the two-edge
adjacency data instead of being assumed. -/
theorem isCPathPair_of_adj (hinj : Function.Injective f) {i j : Fin m} (hij : i ≠ j) {x : V}
    (hxC : x ∉ C) (hxi : G.Adj (f i) x) (hxj : G.Adj (f j) x) :
    IsCPathPair G m 1 1 f i j C hCmem x (edgePath (f i) x) (edgePath (f j) x) := by
  have hmem (a b : V) (u : V) (hu : u ∈ IsCPath.supset (edgePath a b)) : u = a ∨ u = b := by
    rw [IsCPath.mem_supset] at hu
    obtain ⟨k, hk⟩ := hu
    by_cases hk0 : k.val = 0
    · left
      have hk' : k = ⟨0, Nat.zero_lt_succ 1⟩ := Fin.eq_of_val_eq hk0
      rw [← hk, hk', edgePath_zero]
    · right
      have hk1 : k.val = 1 := by have := k.isLt; omega
      have hk' : k = ⟨1, Nat.lt_succ_self 1⟩ := Fin.eq_of_val_eq hk1
      rw [← hk, hk', edgePath_one]
  have hfi : f i ≠ f j := fun h => hij (hinj h)
  refine ⟨IsCPath_edgePath hxC hxi, IsCPath_edgePath hxC hxj, hij, ?_⟩
  intro u hu hu'
  rcases hmem (f i) x u hu with h1 | h1
  · rcases hmem (f j) x u hu' with h2 | h2
    · exact absurd (h1.symm.trans h2) hfi
    · exact Or.inr (Or.inr h2)
  · exact Or.inr (Or.inr h1)

/-- **A SHORTEST ODD CYCLE IS THICK.**

Let `C` be a shortest odd cycle of `G` carried by `f : Fin m → V`, and let `x` have two internally
vertex-disjoint `C`-paths to `f i`, `f j` (of lengths `d1`, `d2`).  If the arc of `C` of length `e`
from `f j` to `f i` is **odd**, then

> `m ≤ e + d1 + d2`.

Indeed the closed walk along that arc is an odd cycle of `G` (`arcPair_isOddCycle`) with exactly
`e + d1 + d2` vertices (`card_arcPair`), and `C` is shortest.  This is the classical observation
that the two attachment points of a fan at a shortest odd cycle are *far apart* along the odd
direction: the fan case forces that arc to have length exactly `m - 2`
(`oddArc_eq_two_of_fan_of_shortest`). -/
theorem arc_sum_ge_of_shortest [Fintype V] (hm : m % 2 = 1) (f : Fin m → V)
    (hinj : Function.Injective f) (hcyc : ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)))
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y)
    (hshort : ∀ D : Finset V, IsOddCycle G D → m ≤ D.card)
    (h : IsCPathPair G m d1 d2 f i j C hCmem x p q)
    (hem : e < m) (hdij : ((cycSucc^[e] : Fin m → Fin m) j) = i)
    (hmod : (e + d1 + d2) % 2 = 1) : m ≤ e + d1 + d2 := by
  have hD : IsOddCycle G ((Finset.univ : Finset (Fin (e + d1 + d2))).image (arcPairFun e f j p q)) :=
    arcPair_isOddCycle hm f hinj hcyc hCmem h hem hdij hmod
  have hle := hshort _ hD
  rw [card_arcPair h hem hinj] at hle
  exact hle

/-- **THE ODD ARC OF A FAN AT A SHORTEST ODD CYCLE HAS LENGTH EXACTLY `m - 2`.**

In the fan case (`d1 = d2 = 1`, i.e. `x` is adjacent to both attachment points) the odd arc of
`arc_sum_ge_of_shortest` satisfies `m - 2 ≤ e ≤ m - 1`; but `e` and `m` are both odd, so `e ≠ m - 1`
and `e = m - 2`.  Equivalently: **the two neighbours of `x` on a shortest odd cycle are exactly two
steps apart.** -/
theorem oddArc_eq_two_of_fan_of_shortest [Fintype V] (hm : m % 2 = 1) (f : Fin m → V)
    (hinj : Function.Injective f) (hcyc : ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)))
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y)
    (hshort : ∀ D : Finset V, IsOddCycle G D → m ≤ D.card)
    {i j : Fin m} (hij : i ≠ j) {x : V} (hxC : x ∉ C) (hxi : G.Adj (f i) x)
    (hxj : G.Adj (f j) x) (hem : e < m)
    (hdij : ((cycSucc^[e] : Fin m → Fin m) j) = i) (hmod : (e + 1 + 1) % 2 = 1) :
    e = m - 2 := by
  have hle := arc_sum_ge_of_shortest hm f hinj hcyc hCmem hshort
    (isCPathPair_of_adj hinj hij hxC hxi hxj) hem hdij hmod
  rcases em (e = m - 2) with h | h
  · exact h
  exfalso
  have h1 : e = m - 1 := by omega
  omega

/-- **THE SHORT-ARC LEMMA, FROM MADER'S TWO-ATTACHMENT LEMMA.**

If `C` is a shortest odd cycle of `G` of length `m`, and `x ∉ C` is adjacent to two distinct
vertices `f i`, `f j` of `C`, then

> `((cycSucc^[2] : Fin m → Fin m) i) = j`  or  `((cycSucc^[2] : Fin m → Fin m) j) = i`.

This is `JSPProblem/Fan.lean`'s `shortArc_of_shortest`, obtained here from the **two-path** arc
cycle and its vertex count (`arc_sum_ge_of_shortest`) instead of from the one-edge arc cycle — an
independent route to the same conclusion, and a check on the new machinery. -/
theorem shortArc_of_pairFan [Fintype V] (hm : m % 2 = 1) (f : Fin m → V)
    (hinj : Function.Injective f)
    (hcyc : ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)))
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ k : Fin m, f k = y)
    (hshort : ∀ D : Finset V, IsOddCycle G D → m ≤ D.card) {i j : Fin m} (hij : i ≠ j) {x : V}
    (hxC : x ∉ C) (hxi : G.Adj (f i) x) (hxj : G.Adj (f j) x) :
    ((cycSucc^[2] : Fin m → Fin m) i) = j ∨ ((cycSucc^[2] : Fin m → Fin m) j) = i := by
  obtain ⟨e, he0, hem, hdij⟩ := exists_arc (m := m) (by omega) hij
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have h1 : m ≤ 1 := by omega
    have hs : Subsingleton (Fin m) := by
      constructor
      intro a b
      apply Fin.ext
      omega
    exact absurd (hs.elim i j) hij
  rcases arc_parity (m := m) hm hij e hem hdij with heod | heod
  · -- the arc `i → j` is odd: the fan read in the other order says `e = m - 2`, whence `j → i`
    -- is an arc of length `2`
    refine Or.inr ?_
    have h2 := oddArc_eq_two_of_fan_of_shortest hm f hinj hcyc hCmem hshort
      hij.symm hxC hxj hxi hem hdij (by omega)
    have h3 : (m - 2) < m := by omega
    have h4 : ((cycSucc^[m - 2] : Fin m → Fin m) i) = j := h2 ▸ hdij
    have h5 : m - (m - 2) = 2 := by omega
    exact h5 ▸ arc_rev h3 h4
  · -- the arc `j → i` is odd and of length `m - e`, so `m - e = m - 2`, i.e. `e = 2`
    refine Or.inl ?_
    have h2 := oddArc_eq_two_of_fan_of_shortest hm f hinj hcyc hCmem hshort
      hij hxC hxi hxj (by omega) (arc_rev hem hdij) (by omega)
    have h3 : e = 2 := by omega
    exact h3 ▸ hdij

end Thick

/-! ### Part 6 — the two-attachment hypothesis is **not** automatic: a machine-checked obstruction -/

section Witness

local instance instDecidableEqWitness1 : DecidableEq (Fin 3 × Fin 1) := Classical.decEq _
local instance instDecidableEqWitness2 : DecidableEq (Fin 3 × Fin 2) := Classical.decEq _

/-- **THE TWO-ATTACHMENT HYPOTHESIS HOLDS ON `kTriangles 1`.**

The single triangle `C` of `kTriangles 1 = K_3` meets every odd cycle of the graph in three
vertices: every odd cycle of `kTriangles k` is a whole fibre (`exists_eq_tri_of_isOddCycle_kTriangles`)
and `kTriangles 1` has one fibre.  So `C` is a two-attachment cycle and round 111's transversal
gives `CloseToBipartite (3 - 1) = CloseToBipartite 2` — the hypothesis is satisfiable, so the
negative result below is not vacuous. -/
theorem twoAttach_kTriangles_one : CloseToBipartite 2 (kTriangles 1) := by
  have hatt : ∀ D : Finset (Fin 3 × Fin 1), IsOddCycle (kTriangles 1) D →
      2 ≤ (D ∩ tri (⟨0, by decide⟩ : Fin 1)).card := by
    intro D hD
    obtain ⟨i, hD⟩ := exists_eq_tri_of_isOddCycle_kTriangles hD
    have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by have := i.isLt; omega)
    rw [hi] at hD
    rw [hD, Finset.inter_self]
    have h3 : (tri (⟨0, by decide⟩ : Fin 1)).card = 3 := card_tri _
    omega
  have h := closeToBipartite_of_twoAttach (C := tri (⟨0, by decide⟩ : Fin 1)) (isOddCycle_tri _) hatt
  have h31 : (3 : ℕ) - 1 = 2 := rfl
  rw [card_tri, h31] at h
  exact h

/-- **MACHINE-CHECKED NEGATIVE RESULT: NO ODD CYCLE OF `kTriangles 2` IS TWO-ATTACHED.**

The hypothesis of `closeToBipartite_of_twoAttach` — *one odd cycle meets every odd cycle of `G` in
at least two vertices* — is **false** on the disjoint union of two triangles: whatever odd cycle
`C` is chosen, the other triangle is an odd cycle disjoint from it.  So the two-attachment
transversal is not a consequence of Erdős's hypothesis, nor of bounded degree, nor of 2-connected
structure: it needs real content, and Mader's lemma above is what produces that content in the
depth-two case. -/
theorem not_twoAttach_kTriangles_two :
    ¬ ∃ (C : Finset (Fin 3 × Fin 2)), IsOddCycle (kTriangles 2) C
      ∧ (∀ D : Finset (Fin 3 × Fin 2), IsOddCycle (kTriangles 2) D → 2 ≤ (D ∩ C).card) := by
  rintro ⟨C, hC, hatt⟩
  obtain ⟨i, hC⟩ := exists_eq_tri_of_isOddCycle_kTriangles hC
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := by
    by_cases hi0 : i = (⟨0, by decide⟩ : Fin 2)
    · refine ⟨⟨1, by decide⟩, fun h => absurd (h ▸ hi0) (by decide)⟩
    · exact ⟨⟨0, by decide⟩, fun h => hi0 h.symm⟩
  have hD : IsOddCycle (kTriangles 2) (tri j) := isOddCycle_tri j
  have hle := hatt (tri j) hD
  have hempty : tri j ∩ tri i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    rw [Finset.mem_inter] at hu
    exact absurd ((mem_tri.mp hu.1).symm.trans (mem_tri.mp hu.2)) hj
  rw [hC, hempty, Finset.card_empty] at hle
  omega

end Witness


end

end JSP90
