/-
# JSP-000090 — the fan lemma around a shortest odd cycle

`JSPProblem/Transversal.lean` reduced the whole of Erdős Problem #73 to the single research
statement `OddCycleErdosPosa r` (bounded odd cycle packing number ⇒ bounded odd cycle
transversal) and proved it for `r = 0` and for the whole class of graphs of bounded odd girth.

This file is a **new attack family** on that statement.  It does not use Mathlib's connectivity,
Menger or fan API (none of which is present in the pinned import slice at all); instead it
develops, from scratch and entirely self-contained, the *local* half of the classical fan
argument:

1. **Arcs.**  Between two vertices of a cyclic ordering there are exactly two arcs; `exists_arc`
   finds the one whose length is `< m`, `arc_rev` identifies the other, and `arc_parity` shows
   that on an *odd* cycle exactly one of the two arcs has odd length.
2. **The arc-cycle constructor** (`arc_isOddCycle`): a vertex `x` outside a cycle which is
   adjacent to two of its vertices closes exactly one of the two arcs into a *simple* cycle of
   length `arc + 2`, and this cycle is **odd** exactly when the arc used is odd.  This is the
   parity core of the fan argument: the odd cycle through `x` is obtained by *counting*, no
   connectivity or Menger theorem is involved.
3. **The fan lemma** (`oddCycle_through_fan`): such an `x`, together with two of its neighbours
   on the odd cycle `C`, lies on an odd cycle of `G` with **at most `|C|` vertices**.
4. **The short-arc lemma** (`shortArc_of_shortest`, `oddCycle_through_fan_of_shortest`): if `C`
   is a *shortest* odd cycle and `|C| ≥ 5`, then the odd cycle of step 3 has **exactly `|C|`
   vertices**, and consequently the two neighbours of `x` on `C` are at cyclic distance exactly
   `2` — so, in particular, an outside vertex never sees two *consecutive* vertices of a shortest
   odd cycle of length `≥ 5`.
5. **A 2-cut corollary** (`card_inter_neigh_le_two`): a vertex outside a shortest odd cycle of
   length `≥ 5` meets that cycle in **at most two** vertices.  (Three neighbours would be pairwise
   at distance exactly `2` around an odd cycle, which is impossible.)

Steps 1–5 are the local lemmas the classical proofs of Erdős–Pósa for odd cycles are built from
(Lovász 1965 for `r = 1`; Reed–Robertson–Seymour–Thomas for general `r`).  What is still missing
after this file is the *global* half: turning the local structure into a bound on a transversal.
That global statement is exactly `JSP90.OddCycleErdosPosa`, and it remains open in this
development (see `discovery/JSP-000090/policy.json`).
-/

import JSPProblem.Transversal
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-! ### Arithmetic on indices around a cycle -/

section Arith

/-- **Cancellation of a common shift modulo `m`.**  If `b, b' < m` and `a + b` and `a + b'` have
the same residue modulo `m`, then `b = b'`.  This is the only modular fact needed below. -/
theorem mod_inj_add {m a b b' : ℕ} (hb : b < m) (hb' : b' < m)
    (h : (a + b) % m = (a + b') % m) : b = b' := by
  have h' : a + b ≡ a + b' [MOD m] := h
  have h2 : b ≡ b' [MOD m] := Nat.ModEq.add_left_cancel' a h'
  exact Nat.ModEq.eq_of_lt_of_lt h2 hb hb'

/-- **Distinct short arcs out of a vertex of a cycle are distinct.**  Iterating the cyclic
successor `p` and `q` times (`p, q < m`) gives different vertices. -/
theorem cycSucc_pow_inj {m : ℕ} (a : Fin m) {p q : ℕ} (hp : p < m) (hq : q < m) (hne : p ≠ q) :
    ((cycSucc^[p] : Fin m → Fin m) a) ≠ ((cycSucc^[q] : Fin m → Fin m) a) := by
  intro he
  have hval : (a.val + p) % m = (a.val + q) % m := by
    have := congrArg Fin.val he
    simpa only [cycSucc_pow_val] using this
  exact hne (mod_inj_add hp hq hval)

/-- **Iterating `m` times around the cycle is the identity**, hence if `d < m` and `d` steps take
`i` to `j`, then `m - d` steps take `j` back to `i`. -/
theorem arc_rev {m : ℕ} {i j : Fin m} {d : ℕ} (hdm : d < m)
    (hdij : (cycSucc^[d] : Fin m → Fin m) i = j) :
    ((cycSucc^[m - d] : Fin m → Fin m) j = i) := by
  have h1 : ((cycSucc^[m] : Fin m → Fin m) i = i) := cycSucc_pow i
  have h2 : (cycSucc^[m - d + d] : Fin m → Fin m) i
      = (cycSucc^[m - d] : Fin m → Fin m) ((cycSucc^[d] : Fin m → Fin m) i) :=
    Function.iterate_add_apply cycSucc (m - d) d i
  have h3 : m - d + d = m := Nat.sub_add_cancel (Nat.le_of_lt hdm)
  rw [h3, h1] at h2
  rw [hdij] at h2
  exact h2.symm

/-- **Every vertex of a cycle is reached from every other vertex by a strictly positive number of
steps smaller than the length of the cycle.**  (The `m` short arcs out of `i` are pairwise
distinct — `cycSucc_pow_inj` — and `Fin m` has `m` elements.) -/
theorem exists_arc {m : ℕ} (hm : 0 < m) {i j : Fin m} (hij : i ≠ j) :
    ∃ d : ℕ, 0 < d ∧ d < m ∧ ((cycSucc^[d] : Fin m → Fin m) i = j) := by
  classical
  set S : Finset (Fin m) := (Finset.univ : Finset (Fin m)).image
    (fun k : Fin m => ((cycSucc^[k.val] : Fin m → Fin m) i)) with hSdef
  have hcard : S.card = m := by
    rw [hSdef, Finset.card_image_of_injective]
    · simp
    · intro a b hab
      apply Fin.ext
      have hv : (i.val + a.val) % m = (i.val + b.val) % m := by
        have h := congrArg Fin.val hab
        simpa only [cycSucc_pow_val] using h
      exact mod_inj_add a.isLt b.isLt hv
  have hS : S = (Finset.univ : Finset (Fin m)) :=
    Finset.eq_univ_of_card S (hcard.trans (Fintype.card_fin m).symm)
  have hjmem : j ∈ S := by rw [hS]; exact Finset.mem_univ j
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hjmem
  have hpos : 0 < k.val := by
    by_contra hcon
    have hk0 : k.val = 0 := Nat.eq_zero_of_not_pos hcon
    have h1 : (cycSucc^[k.val] : Fin m → Fin m) i = j := heq
    have h2 : (cycSucc^[k.val] : Fin m → Fin m) i = i := by rw [hk0]; rfl
    exact hij (h2.symm.trans h1)
  exact ⟨k.val, hpos, k.isLt, heq⟩

/-- **The complement of an odd arc in an odd cycle is even and at least `2`.** -/
theorem even_compl_of_odd {m e : ℕ} (hm : m % 2 = 1) (he : e % 2 = 1) (hem : e < m) :
    (m - e) % 2 = 0 ∧ 2 ≤ m - e := by
  have hsum : m - e + e = m := Nat.sub_add_cancel (Nat.le_of_lt hem)
  have hmod : ((m - e) % 2 + e % 2) % 2 = m % 2 := by
    have hadd := Nat.add_mod (m - e) e 2
    rw [hsum] at hadd
    exact hadd.symm
  rw [he] at hmod
  rcases Nat.mod_two_eq_zero_or_one (m - e) with hz | ho
  · refine ⟨hz, ?_⟩
    omega
  · rw [ho] at hmod
    exact absurd (hmod.trans hm) (by decide)

/-- **Exactly one of the two arcs between two distinct vertices of an odd cycle is odd.**  The two
arc lengths add up to `m`, which is odd. -/
theorem arc_parity {m : ℕ} (hm : m % 2 = 1) {i j : Fin m} (hij : i ≠ j)
    (d : ℕ) (hdm : d < m) (hdij : (cycSucc^[d] : Fin m → Fin m) i = j) :
    d % 2 = 1 ∨ (m - d) % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · right
    rcases Nat.mod_two_eq_zero_or_one (m - d) with h2 | h2
    · exfalso
      have hsum : m - d + d = m := Nat.sub_add_cancel (Nat.le_of_lt hdm)
      have hmod : ((m - d) % 2 + d % 2) % 2 = m % 2 := by
        have hadd := Nat.add_mod (m - d) d 2
        rw [hsum] at hadd
        exact hadd.symm
      rw [h, h2] at hmod
      have hone : (0 : ℕ) % 2 = 0 := rfl
      rw [Nat.zero_add, hone] at hmod
      exact absurd (hmod.trans hm) (by decide)
    · exact h2
  · exact Or.inl h

end Arith

/-! ### Closing an arc into a cycle -/

section Arc

/-- **The closed walk `x → f i → f (cycSucc i) → … → f (cycSucc^[d-1] i) → x`**, viewed as a map
`Fin (d + 2) → V`: entry `0` is `x`, and entry `k + 1` is `f (cycSucc^[k] i)`. -/
def arcFun (m d : ℕ) (f : Fin m → V) (i : Fin m) (x : V) (j : Fin (d + 2)) : V :=
  if j.val = 0 then x else f ((cycSucc^[j.val - 1] : Fin m → Fin m) i)

@[simp] theorem arcFun_zero {m d : ℕ} (f : Fin m → V) (i : Fin m) (x : V) :
    arcFun m d f i x (0 : Fin (d + 2)) = x := rfl

/-- **The arc-closed walk is a simple cycle**: no vertex is repeated.  Here `x` is outside the
image of `f`, and the interior vertices of the arc are pairwise distinct because they are
different numbers of steps around the cycle (`d < m`). -/
theorem arcFun_inj {m d : ℕ} (hdm : d < m) (f : Fin m → V) (hinj : Function.Injective f)
    (i : Fin m) (x : V) (hximg : ∀ j : Fin m, f j ≠ x) (a b : Fin (d + 2)) (hne : a ≠ b) :
    arcFun m d f i x a ≠ arcFun m d f i x b := by
  by_cases ha0 : a.val = 0
  · by_cases hb0 : b.val = 0
    · intro hab
      exact hne (Fin.ext (ha0.trans hb0.symm))
    · intro hab
      rw [arcFun, if_pos ha0, arcFun, if_neg hb0] at hab
      exact (hximg _ hab.symm).elim
  · by_cases hb0 : b.val = 0
    · intro hab
      rw [arcFun, if_neg ha0, arcFun, if_pos hb0] at hab
      exact (hximg _ hab).elim
    · intro hab
      rw [arcFun, if_neg ha0, arcFun, if_neg hb0] at hab
      have hh : ((cycSucc^[a.val - 1] : Fin m → Fin m) i)
          = ((cycSucc^[b.val - 1] : Fin m → Fin m) i) := hinj hab
      have hv : (i.val + (a.val - 1)) % m = (i.val + (b.val - 1)) % m := by
        have h := congrArg Fin.val hh
        simpa only [cycSucc_pow_val] using h
      have hsub : a.val - 1 = b.val - 1 := mod_inj_add (by omega) (by omega) hv
      exact hne (Fin.ext (by omega))

/-- **Consecutive entries of the arc-closed walk are adjacent.**  In the bulk of the walk this is
the adjacency of the cycle; at the two ends it is one of the two extra edges through `x`. -/
theorem arcFun_adj {m d : ℕ} (hdm : d < m) (hd0 : 0 < d) (f : Fin m → V) (i : Fin m) (x : V)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) (hxi : G.Adj x (f i))
    (hlast : G.Adj (f ((cycSucc^[d] : Fin m → Fin m) i)) x) :
    ∀ j : Fin (d + 2), G.Adj (arcFun m d f i x j) (arcFun m d f i x (cycSucc j)) := by
  intro j
  have hcs : (cycSucc j).val = (j.val + 1) % (d + 2) := cycSucc_val j
  rcases Nat.eq_zero_or_pos j.val with hj | hj
  · -- the walk steps from `x` to the first vertex of the arc
    have h1 : (cycSucc j).val = 1 := by
      rw [hcs, hj, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 : arcFun m d f i x (cycSucc j) = f i := by
      rw [arcFun, h1, if_neg (by omega), show 1 - 1 = 0 from rfl,
        show (cycSucc^[0] : Fin m → Fin m) i = i from rfl]
    have h2a : arcFun m d f i x j = x := by rw [arcFun, if_pos hj]
    rw [h2a, h2]
    exact hxi
  · by_cases hjd : j.val + 1 = d + 2
    · -- the walk closes from the last vertex of the arc back to `x`
      have h1 : (cycSucc j).val = 0 := by
        rw [hcs, hjd, Nat.mod_self]
      have h2 : arcFun m d f i x j = f ((cycSucc^[d] : Fin m → Fin m) i) := by
        rw [arcFun, if_neg (by omega), show j.val - 1 = d by omega]
      have h3 : arcFun m d f i x (cycSucc j) = x := by
        rw [arcFun, h1, if_pos rfl]
      rw [h2, h3]
      exact hlast
    · -- a step inside the arc
      have hjlt : j.val + 1 < d + 2 := by omega
      have h1 : (cycSucc j).val = j.val + 1 := by
        rw [hcs, Nat.mod_eq_of_lt hjlt]
      have h2 : arcFun m d f i x j = f ((cycSucc^[j.val - 1] : Fin m → Fin m) i) := by
        rw [arcFun, if_neg (Nat.ne_of_gt hj)]
      have h3 : arcFun m d f i x (cycSucc j) = f ((cycSucc^[j.val] : Fin m → Fin m) i) := by
        rw [arcFun, h1, if_neg (by omega),
          show j.val + 1 - 1 = j.val from Nat.add_sub_cancel j.val 1]
      have hstep : ((cycSucc^[j.val] : Fin m → Fin m) i)
          = cycSucc ((cycSucc^[j.val - 1] : Fin m → Fin m) i) := by
        have h := Function.iterate_succ_apply' cycSucc (j.val - 1) i
        have heq : ((j.val - 1 : ℕ).succ) = j.val := by omega
        rw [heq] at h
        exact h
      rw [h2, h3, hstep]
      exact hcyc ((cycSucc^[j.val - 1] : Fin m → Fin m) i)

/-- **The arc-cycle constructor (the parity core of the fan argument).**

Let `C` be an odd cycle of `G` carried by an injective cyclic ordering `f : Fin m → V` with
`m` odd and `m ≥ 3`, let `x` be a vertex outside `C`, let `i : Fin m`, let `d` satisfy
`0 < d < m`, and suppose `x` is adjacent to `f i` and to `f (cycSucc^[d] i)`.  If `d` is odd, then
the arc of `C` of length `d` between those two vertices, closed up through `x`, is a **simple odd
cycle** of `G` of exactly `d + 2` vertices.

This is the statement that makes fan arguments possible without Menger's theorem: the parity of
the two cycles obtained from the two arcs is *opposite*, so exactly one of them is odd, and the odd
one is found by counting. -/
theorem arc_isOddCycle {m d : ℕ} {C : Finset V} (hm : m % 2 = 1) (hm3 : 3 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {i : Fin m} (hdm : d < m) (hd0 : 0 < d)
    {x : V} (hxC : x ∉ C) (hxi : G.Adj x (f i))
    (hlast : G.Adj (f ((cycSucc^[d] : Fin m → Fin m) i)) x) (hdodd : d % 2 = 1) :
    IsOddCycle G ((Finset.univ : Finset (Fin (d + 2))).image (arcFun m d f i x)) := by
  have hximg : ∀ j : Fin m, f j ≠ x := by
    intro j hj
    have hfj : f j ∈ C := (hCmem (f j)).mpr ⟨j, rfl⟩
    rw [hj] at hfj
    exact hxC hfj
  have hmod : (d + 2) % 2 = 1 := by
    have h := Nat.mod_add_mod d 2 2
    rw [← h, hdodd]
  have hinjarc : Function.Injective (arcFun m d f i x) := by
    intro a b hab
    by_contra hne
    exact False.elim ((arcFun_inj hdm f hinj i x hximg a b hne) hab)
  refine ⟨d + 2, arcFun m d f i x, hmod, by omega, hinjarc, ?_, ?_⟩
  · exact arcFun_adj hdm hd0 f i x hcyc hxi hlast
  · intro y
    constructor
    · intro hy
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
      exact ⟨j, hj⟩
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **Cardinality of the arc cycle.** -/
theorem arc_card {m d : ℕ} (hdm : d < m) (f : Fin m → V) (hinj : Function.Injective f)
    (i : Fin m) (x : V) (hximg : ∀ j : Fin m, f j ≠ x) :
    ((Finset.univ : Finset (Fin (d + 2))).image (arcFun m d f i x)).card = d + 2 := by
  have hinjarc : Function.Injective (arcFun m d f i x) := by
    intro a b hab
    by_contra hne
    exact False.elim
      ((arcFun_inj (m := m) hdm f hinj i x hximg a b hne) hab)
  rw [Finset.card_image_of_injective _ hinjarc]
  simp

/-- **The card of a cycle carried by `f` is the length of the cycle.** -/
theorem card_eq_cyclicOrder {m : ℕ} {C : Finset V} (f : Fin m → V) (hinj : Function.Injective f)
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) : C.card = m := by
  have heq : C = (Finset.univ : Finset (Fin m)).image f := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hCmem]
  rw [heq, Finset.card_image_of_injective _ hinj]
  simp

end Arc

/-! ### The fan lemma -/

section Fan

/-- **The fan lemma.**  Let `C` be an odd cycle of `G` (carried by a cyclic ordering `f`), let `x`
be a vertex outside `C` adjacent to two *distinct* vertices `f i` and `f j` of `C`.  Then there is
an odd cycle `D` of `G` with `x ∈ D`, `f i ∈ D`, `f j ∈ D`, and `|D| ≤ |C|`.

Proof: take the arc of `C` between `f i` and `f j` whose length is odd (`arc_parity`) and close
it up through `x` (`arc_isOddCycle`); the resulting cycle has `arc + 2` vertices, and an odd
`arc < m` in an odd cycle of length `m` satisfies `arc + 2 ≤ m`. -/
theorem oddCycle_through_fan {m : ℕ} {C : Finset V} (hm : m % 2 = 1) (hm3 : 3 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x)
    {i j : Fin m} (hij : i ≠ j) {x : V} (hxC : x ∉ C) (hxi : G.Adj x (f i)) (hxj : G.Adj x (f j)) :
    ∃ (D : Finset V), IsOddCycle G D ∧ x ∈ D ∧ f i ∈ D ∧ f j ∈ D ∧ D.card ≤ C.card := by
  have hximg : ∀ k : Fin m, f k ≠ x := by
    intro k hk
    have hfk : f k ∈ C := (hCmem (f k)).mpr ⟨k, rfl⟩
    rw [hk] at hfk
    exact hxC hfk
  have hCcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  obtain ⟨d, hd0, hdm, hdij⟩ := exists_arc (by omega) hij
  -- an odd arc of odd length `< m` in an odd cycle of length `m` has length at most `m - 2`
  have key : ∀ e : ℕ, e % 2 = 1 → e < m → e + 2 ≤ m := by
    intro e he hem
    have h2le := (even_compl_of_odd hm he hem).2
    omega
  rcases arc_parity hm hij d hdm hdij with hdodd | hdodd
  · -- the arc `i → j` is odd
    refine ⟨(Finset.univ : Finset (Fin (d + 2))).image (arcFun m d f i x),
      arc_isOddCycle hm hm3 f hinj hcyc hCmem hdm hd0 hxC hxi
        (by rw [hdij]; exact hxj.symm) hdodd, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    · rw [← hdij]
      exact Finset.mem_image.mpr ⟨⟨d + 1, by omega⟩, Finset.mem_univ _, rfl⟩
    · rw [arc_card hdm f hinj i x hximg]
      exact Nat.le_trans (key d hdodd hdm) (by omega)
  · -- the arc `j → i` is odd
    have hje : ((cycSucc^[m - d] : Fin m → Fin m) j = i) := arc_rev hdm hdij
    refine ⟨(Finset.univ : Finset (Fin ((m - d) + 2))).image (arcFun m (m - d) f j x),
      arc_isOddCycle hm hm3 f hinj hcyc hCmem (by omega) (by omega) hxC hxj
        (by rw [hje]; exact hxi.symm) hdodd, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · rw [← hje]
      exact Finset.mem_image.mpr
        ⟨⟨(m - d) + 1, by omega⟩, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, rfl⟩
    · rw [arc_card (by omega) f hinj j x hximg]
      exact Nat.le_trans (key (m - d) hdodd (by omega)) (by omega)

/-- **The fan lemma at a shortest odd cycle.**  If `C` is a *shortest* odd cycle of `G` with
`|C| ≥ 5`, the odd cycle of `oddCycle_through_fan` has **exactly `|C|` vertices**. -/
theorem oddCycle_through_fan_of_shortest {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x)
    {i j : Fin m} (hij : i ≠ j) {x : V} (hxC : x ∉ C) (hxi : G.Adj x (f i)) (hxj : G.Adj x (f j)) :
    ∃ (D : Finset V), IsOddCycle G D ∧ x ∈ D ∧ f i ∈ D ∧ f j ∈ D ∧ D.card = C.card := by
  obtain ⟨D, hD, hx, hi, hj, hle⟩ :=
    oddCycle_through_fan hm (by omega) f hinj hcyc hCmem hij hxC hxi hxj
  exact ⟨D, hD, hx, hi, hj, Nat.le_antisymm hle (hshort D hD)⟩

/-- **The short-arc lemma.**  Let `C` be a *shortest* odd cycle of `G` with `|C| ≥ 5`, let
`x ∉ V(C)` be adjacent to `f i` and `f j` with `i ≠ j`.  Then `f i` and `f j` are at cyclic
distance exactly `2`: one of `j = cycSucc (cycSucc i)` or `i = cycSucc (cycSucc j)` holds.

In words: **an outside vertex of a shortest odd cycle of length at least `5` sees the cycle only
through pairs of vertices two steps apart — never through two consecutive vertices.**  This is the
local structural lemma from which fan arguments are built: a genuine fan would produce a shorter
odd cycle. -/
theorem shortArc_of_shortest {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x)
    {i j : Fin m} (hij : i ≠ j) {x : V} (hxC : x ∉ C) (hxi : G.Adj x (f i)) (hxj : G.Adj x (f j)) :
    cycSucc (cycSucc i) = j ∨ cycSucc (cycSucc j) = i := by
  have hximg : ∀ k : Fin m, f k ≠ x := by
    intro k hk
    have hfk : f k ∈ C := (hCmem (f k)).mpr ⟨k, rfl⟩
    rw [hk] at hfk
    exact hxC hfk
  have hCcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  obtain ⟨d, hd0, hdm, hdij⟩ := exists_arc (by omega) hij
  -- minimality forces every odd arc to have length at least `m - 2`
  have key : d % 2 = 1 → d + 2 ≥ m := by
    intro he
    have hD : IsOddCycle G ((Finset.univ : Finset (Fin (d + 2))).image (arcFun m d f i x)) :=
      arc_isOddCycle hm (by omega) f hinj hcyc hCmem hdm hd0 hxC hxi
        (by rw [hdij]; exact hxj.symm) he
    have hle := hshort _ hD
    rw [arc_card hdm f hinj i x hximg, hCcard] at hle
    exact hle
  have key2 : (m - d) % 2 = 1 → (m - d) + 2 ≥ m := by
    intro he
    have hD : IsOddCycle G ((Finset.univ : Finset (Fin ((m - d) + 2))).image
        (arcFun m (m - d) f j x)) :=
      arc_isOddCycle hm (by omega) f hinj hcyc hCmem (by omega) (by omega) hxC hxj
        (by rw [arc_rev hdm hdij]; exact hxi.symm) he
    have hle := hshort _ hD
    rw [arc_card (by omega) f hinj j x hximg, hCcard] at hle
    exact hle
  have htwo {a b : Fin m} {e : ℕ} (he : e = 2)
      (h : (cycSucc^[e] : Fin m → Fin m) a = b) : ((cycSucc^[2] : Fin m → Fin m) a = b) := by
    rw [← h, he]
  rcases arc_parity hm hij d hdm hdij with hdodd | hdodd
  · -- the `i → j` arc is odd, hence of length `m - 2`, so the `j → i` arc has length `2`
    right
    exact htwo (e := m - d) (by have := key hdodd; omega) (arc_rev hdm hdij)
  · -- the `j → i` arc is odd, hence of length `m - 2`, so the `i → j` arc has length `2`
    left
    exact htwo (e := d) (by have := key2 hdodd; omega) hdij

/-- **The short-arc lemma, pairwise form.**  Let `C` be a shortest odd cycle with `5 ≤ |C|`, let
`x ∉ V(C)`, and let `f a`, `f b` be two distinct neighbours of `x` on `C`.  Then `b` is the cyclic
successor of the cyclic successor of `a`, or conversely.  In other words the two attachment
points of a fan on `C` are always exactly two steps apart. -/
theorem neigh_pair_close_of_shortest {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxC : x ∉ C) {a b : Fin m}
    (ha : G.Adj x (f a)) (hb : G.Adj x (f b)) (hne : a ≠ b) :
    cycSucc (cycSucc a) = b ∨ cycSucc (cycSucc b) = a :=
  shortArc_of_shortest hshort hm hm3 f hinj hcyc hCmem hne hxC ha hb

/-- **No outside vertex sees three vertices of a shortest odd cycle of length at least `5`.**
Every set of neighbours of a vertex `x ∉ V(C)` on a shortest odd cycle `C` with `5 ≤ |C|` has at
most two members.

Indeed, if `x` were adjacent to `f a`, `f b`, `f c` with the three indices pairwise distinct, then
by `shortArc_of_shortest` each pair of indices is related by the rotation `T = (cycSucc ∘ cycSucc)`
by `+2` around the cycle; three pairwise distinct indices cannot satisfy this on an odd cycle of
length `≥ 5`, because `T^[3] = id` would force `m ∣ 6`. -/
theorem card_inter_neigh_le_two {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxC : x ∉ C) :
    ∀ (S : Finset (Fin m)), (∀ j ∈ S, G.Adj x (f j)) → S.card ≤ 2 := by
  classical
  intro S hS
  -- the rotation by two positions around the cycle
  set T : Fin m → Fin m := fun a => ⟨(a.val + 2) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm3)⟩
    with hT
  have hTval : ∀ a : Fin m, (T a).val = (a.val + 2) % m := fun _ => rfl
  have hTinj : Function.Injective T := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    simp only [hTval] at h
    have h2 : (2 + a.val) % m = (2 + b.val) % m := by
      refine (congrArg (· % m) (Nat.add_comm a.val 2).symm).trans
        (h.trans (congrArg (· % m) (Nat.add_comm b.val 2)))
    exact mod_inj_add a.isLt b.isLt h2
  have hstep : ∀ a b : Fin m, cycSucc (cycSucc a) = b → T a = b := by
    intro a b h
    have h1 : ((cycSucc^[2] : Fin m → Fin m) a) = cycSucc (cycSucc a) := by
      have h := Function.iterate_succ_apply' cycSucc 1 a
      rw [show ((1 : ℕ).succ) = 2 from rfl,
        show (cycSucc^[1] : Fin m → Fin m) a = cycSucc a from rfl] at h
      exact h
    have hv : (a.val + 2) % m = b.val := by
      have h := congrArg Fin.val h
      rw [h1.symm] at h
      simpa only [cycSucc_pow_val] using h
    exact Fin.ext hv
  -- `T^[3] z = z` forces `m ∣ 6`, impossible for odd `m ≥ 5`
  have hT3 : ∀ z : Fin m, (T (T (T z))).val = (z.val + 6) % m := by
    intro z
    calc (T (T (T z))).val = (((z.val + 2) % m + 2) % m + 2) % m := by simp only [hTval]
      _ = ((z.val + 4) % m + 2) % m := by rw [Nat.mod_add_mod (z.val + 2) m 2]
      _ = (z.val + 6) % m := by rw [Nat.mod_add_mod (z.val + 4) m 2]
  have hdvd : ∀ z : Fin m, T (T (T z)) = z → m ∣ 6 := by
    intro z hz
    have hq := Nat.mod_add_div (z.val + 6) m
    have hmod : (z.val + 6) % m = z.val := by
      have h := congrArg Fin.val hz
      rwa [hT3 z] at h
    refine ⟨(z.val + 6) / m, ?_⟩
    omega
  have hnoT3 : ∀ z : Fin m, T (T (T z)) ≠ z := by
    intro z hz
    obtain ⟨c, hc⟩ := hdvd z hz
    have hc1 : c ≥ 1 := by
      by_contra hcon
      have : c = 0 := Nat.eq_zero_of_not_pos hcon
      subst this
      omega
    have hle : m ≤ 6 := by
      have h2 := Nat.mul_le_mul (le_refl m) hc1
      omega
    have hm5 : m = 5 := by omega
    have hbad : ¬ ((5 : ℕ) ∣ 6) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      decide
    exact hbad (by rw [← hm5]; exact ⟨c, by omega⟩)
  -- three pairwise distinct indices pairwise related by `T` cannot exist
  have htriple : ∀ a b c : Fin m, a ≠ b → a ≠ c → b ≠ c →
      (T a = b ∨ T b = a) → (T a = c ∨ T c = a) → (T b = c ∨ T c = b) → False := by
    intro a b c hab hac hbc h1 h2 h3
    rcases h1 with h1 | h1
    · have h4 : T c = a := by
        rcases h2 with h2 | h2
        · exact absurd (h1.symm.trans h2) hbc
        · exact h2
      have h5 : T b = c := by
        rcases h3 with h3 | h3
        · exact h3
        · exact absurd (h4.symm.trans h3) hab
      exact hnoT3 a (by rw [h1, h5, h4])
    · have h4 : T a = c := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd (hTinj (h1.trans h2.symm)) hbc
      have h5 : T c = b := by
        rcases h3 with h3 | h3
        · exact absurd (h1.symm.trans h3) hac
        · exact h3
      exact hnoT3 b (by rw [h1, h4, h5])
  -- conclude
  by_contra hcon
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨t, htS, htcard⟩ := Finset.le_card_iff_exists_subset_card.mp h3
  obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp htcard
  have hza : a ∈ S := htS (by rw [hteq]; exact Finset.mem_insert_self _ _)
  have hzb : b ∈ S := htS (by rw [hteq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hzc : c ∈ S := htS (by
    rw [hteq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c)))
  have h1 := neigh_pair_close_of_shortest hshort hm hm3 f hinj hcyc hCmem hxC
    (hS a hza) (hS b hzb) hab
  have h2 := neigh_pair_close_of_shortest hshort hm hm3 f hinj hcyc hCmem hxC
    (hS a hza) (hS c hzc) hac
  have h4 := neigh_pair_close_of_shortest hshort hm hm3 f hinj hcyc hCmem hxC
    (hS b hzb) (hS c hzc) hbc
  exact htriple a b c hab hac hbc
    ((h1.elim (fun h => Or.inl (hstep _ _ h)) (fun h => Or.inr (hstep _ _ h))))
    ((h2.elim (fun h => Or.inl (hstep _ _ h)) (fun h => Or.inr (hstep _ _ h))))
    ((h4.elim (fun h => Or.inl (hstep _ _ h)) (fun h => Or.inr (hstep _ _ h))))

/-- **The short-arc lemma instantiated at Erdős's local hypothesis.**

If `LocIndep k G` holds and `C` is a *shortest* odd cycle of `G` with `5 ≤ |C|`, then every vertex
of `G` outside `C` meets `C` in at most two vertices, and any two of its attachment points are two
steps apart along `C`.  So the shortest odd cycle of a graph satisfying Erdős #73's hypothesis is
"2-attached": it is a genuine 2-cut of the local structure, which is exactly the local shape that
fan arguments for Erdős–Pósa exploit. -/
theorem locIndep_shortest_attach [Fintype V] {k : ℕ} {C : Finset V} (_hG : LocIndep k G)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (_hm : C.card % 2 = 1) (hm3 : 5 ≤ C.card) (f : Fin C.card → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin C.card, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin C.card, f j = x) {x : V} (hxC : x ∉ C) :
    ∀ S : Finset (Fin C.card), (∀ j ∈ S, G.Adj x (f j)) → S.card ≤ 2 :=
  card_inter_neigh_le_two hshort _hm hm3 f hinj hcyc hCmem hxC

end Fan

end

end JSP90
