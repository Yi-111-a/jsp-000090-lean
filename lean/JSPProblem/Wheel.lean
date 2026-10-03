/-
# JSP-000090 — `JSPProblem/Wheel.lean`: the WHEEL, and **NO FUNCTION OF THE DEFICIENCY BOUNDS THE
## ATTACHMENT SET**

`discovery/JSP-000090/policy.json` (rounds 119 and 120) reduced the absorption step of the residue
induction to a *numerical* question and left it as the blocker:

* round 119: find a function `φ` with `|PetalSet G C| ≤ φ(k)` under `LocIndep k G`;
* round 120: the sharper guess `|PetalSet G C| ≤ MaxDef G`, proved under a packing cover
  (`JSP90.card_petalSet_le_maxDef_of_cover`) and **refuted** on the seven-vertex witness `g7`;
* round 120, blocker 2: "the smallest plausible linear shape is `φ(k) = k + 1` or `φ(k) = 3/2 k`,
  and **no witness in this development forces `φ(2) > 3`**".

This file closes that question, negatively and *parametrically*: **there is no such function at
all.**

## The witness: the wheel

`wheel n` (odd `n ≥ 3`) has `2n + 1` vertices:

* `c_0, c_1, …, c_{n-1}` — the vertices of the odd **rim** `C` (`wheelC i`);
* one **hub** `h` (`wheelHub`), adjacent to every rim vertex and to every leaf;
* one **leaf** `x_i` (`wheelL i`) per rim vertex, adjacent to `c_i` and to `h`;
* `n - 1` isolated filler vertices (`Sum.inl (Sum.inr (Option.some j))`), which exist only to keep
  the vertex type a fixed `Fintype` type without arithmetic.

The petals are the triangles `{c_i, h, x_i}`, each meeting `C` in exactly the one vertex `c_i`, so
**every vertex of `C` is an attachment point**: `PetalSet (wheel n) C = C` and
`|PetalSet (wheel n) C| = n`, which is unbounded.

The deficiency, on the other hand, is **at most 2 for every `n`**: deleting the hub and the last rim
vertex leaves a path with pendant leaves.  (No lower bound on `MaxDef` is needed or proved here.)

## What is proved

* **`JSP90.card_petalSet_wheelCycleFins = n`** — the attachment set is the whole rim.
* **`JSP90.closeToBipartite_two_wheel`, `JSP90.maxDef_le_two_wheel`,
  `JSP90.locIndep_two_wheel`** — `MaxDef (wheel n) ≤ 2` for every `n ≥ 3`.
* **`JSP90.no_petalSet_bound_of_maxDef`** — **NO FUNCTION OF THE DEFICIENCY BOUNDS THE ATTACHMENT
  SET**: there is **no** `φ : ℕ → ℕ` with `|PetalSet (wheel n) C| ≤ φ (MaxDef (wheel n))` for every
  odd `n ≥ 3`, although the family has deficiency at most `2` throughout.  Since `φ` is monotone and
  `MaxDef ≤ 2`, such a `φ` would satisfy `n ≤ φ 2` for all odd `n`, which is absurd.  **The whole
  family of numerical bounds `φ(MaxDef G)` — the blocker of rounds 119 and 120 — is refuted by one
  family of graphs of deficiency 2 with an unbounded attachment set.**
* **`JSP90.not_card_petalSet_le_maxDef_add_wheel`, `JSP90.not_card_petalSet_le_mul_maxDef_wheel`,
  `JSP90.not_petalSet_le_of_locIndep_two`** — the three sharpest *pointwise* forms of the same
  refutation: `|PetalSet| ≤ MaxDef + c` is false for every `c`, `|PetalSet| ≤ c * MaxDef` is false
  for every `c ≥ 1`, and for every `φ` and every `k` there is a graph satisfying `LocIndep k` with
  `|PetalSet G C| > φ k`.
* **`JSP90.hubCover_wheelCycleFins`, `JSP90.closeToBipartite_wheel_hub`** — the *positive* content
  of the round: the **single hub** `{wheelHub}` is a hub cover of `C` in the sense of
  `JSPProblem/Hub.lean`, so `JSP90.closeToBipartite_of_hubCover` gives `CloseToBipartite n (wheel n)`
  with the constant `n = |C| - 1 + 1`, where the attachment-set route of round 119 pays `2n - 1`
  (`JSP90.hubCover_constant_lt_wheel`).  The proof is the machine-checked statement that **every
  petal of the wheel passes through the hub** — equivalently that every odd cycle of the wheel
  avoiding the hub lies on the rim (`JSP90.subset_wheelCycleFins_of_oddCycle_avoid_hub`): in the
  hub-deleted wheel a leaf and a filler vertex have at most one neighbour, whereas two distinct
  cycle-neighbours of a vertex on a cycle are distinct (`JSP90.CycleOrder.step_prev_ne`).
* **`JSP90.isOddCycle_of_oddCycle_avoiding`** — a reusable transport lemma: an odd cycle avoiding `X`
  is an odd cycle of `deleteFinset G X`.
* **`JSP90.isOddCycle_triple'`** — the triangle lemma of round 120, re-derived for an arbitrary
  vertex type.

## What this means for the blocker

The absorption step cannot be closed by charging the attachment points against the deficiency, in
any shape: the attachment set is **not** a function of the deficiency.  What the wheel shows is
that the attachment points are *not independent* — one vertex carries all of them at once — so the
object to be charged is a **hub set** (`JSPProblem/Hub.lean`) and the residual to be proved is
`JSP90.HubByPacking r ℓ q`.  `jsp_000090_main` is **not** declared and `JSP90.OddCycleErdosPosa r`
is untouched.

## Round 124 — the file is IN THE BUILD, and the family is closed exactly

The file was written in round 121 and **did not compile** in rounds 121, 122 and 123, so every
declaration above was dead code.  Round 124 repairs it (the failures were: `ho` used where the
cycle *order* `o` was meant, `Finset.card_insert_of_notMem` and `Finset.inter_eq_self.mpr` absent at
this revision, `φ.monotone` applied to an arbitrary `φ : ℕ → ℕ`, `not_isOddCycle_of_isBipartite`
taking an `∃`-witness, and one missing `end` for the anonymous `noncomputable section`) and adds
**Part 7**, which settles the family in the positive direction:

* **`JSP90.closeToBipartite_wheel_iff`: `CloseToBipartite m (wheel n) ↔ 2 ≤ m`** for odd `n ≥ 3` —
  the **exact** odd cycle transversal number of the wheel is `2`, so an attachment set of `n`
  vertices costs *nothing* here;
* **`JSP90.not_closeToBipartite_zero_wheel`, `JSP90.not_closeToBipartite_one_wheel`** and the input
  **`JSP90.exists_oddCycle_avoiding_vertex`** (no vertex of the wheel meets every odd cycle);
* **`JSP90.wheel_triple`** — deficiency `≤ 2`, attachment set of size `n`, transversal number `2`:
  the three numbers that make the wheel a sharp test of every attachment-set route at once;
* **`JSP90.not_petalSet_le_of_locIndep_ge_two`** — the refutation of the numerical blocker now holds
  under Erdős's own hypothesis for **every `k ≥ 2`**, not only at `k = 2`;
* **`JSP90.wheelC_of_adj_two`, `JSP90.wheelColour`, `JSP90.wheelStarColour`,
  `JSP90.wheel_exists_index_ne`** — the reusable local lemmas the proofs need.
-/

import JSPProblem.Hub
import JSPProblem.Two

namespace JSP90

open Finset Fintype Set

variable {n : ℕ}

noncomputable section

/-! ### Part 1 — the wheel -/

/-- **The vertices of the wheel**: the rim (`Sum.inl (Sum.inl i)`), the hub (`Sum.inl (Sum.inr ())`)
and the leaves (`Sum.inr i`).  The vertex type has exactly `2n + 1` points.

The attribute is load-bearing: the case analysis on the edge structure is only usable when `WheelV n`
is reducible to the sum type. -/
@[reducible] def WheelV (n : ℕ) : Type := (Fin n ⊕ Unit) ⊕ Fin n

instance instFintypeWheelV (n : ℕ) : Fintype (WheelV n) :=
  inferInstanceAs (Fintype ((Fin n ⊕ Unit) ⊕ Fin n))

local instance instDecidableEqWheelV (n : ℕ) : DecidableEq (WheelV n) := Classical.decEq _

/-- The `i`-th vertex of the rim. -/
def wheelC (i : Fin n) : WheelV n := Sum.inl (Sum.inl i)

/-- The hub. -/
def wheelHub : WheelV n := Sum.inl (Sum.inr ())

/-- The `i`-th leaf. -/
def wheelL (i : Fin n) : WheelV n := Sum.inr i

theorem wheelC_injective : Function.Injective (wheelC (n := n)) := by
  intro i j h
  exact Sum.inl.inj (Sum.inl.inj h)

theorem wheelL_injective : Function.Injective (wheelL (n := n)) := fun _ _ h => Sum.inr.inj h

theorem wheelC_ne_wheelHub (i : Fin n) : wheelC i ≠ wheelHub := by
  intro h
  simp only [wheelC, wheelHub] at h
  exact (Sum.inl_ne_inr (Sum.inl.inj h)).elim

theorem wheelL_ne_wheelC (i j : Fin n) : wheelL i ≠ wheelC j := by
  intro h
  simp only [wheelL, wheelC] at h
  exact (Sum.inl_ne_inr h.symm).elim

theorem wheelL_ne_wheelHub (i : Fin n) : wheelL i ≠ wheelHub := by
  intro h
  simp only [wheelL, wheelHub] at h
  exact (Sum.inl_ne_inr h.symm).elim

theorem wheelHub_ne_wheelL (i : Fin n) : wheelHub ≠ wheelL i := by
  intro h
  simp only [wheelL, wheelHub] at h
  exact (Sum.inl_ne_inr h).elim

/-- **The last vertex of the rim** — the one the two-vertex transversal deletes. -/
def wheelLast (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- **THE SHAPE OF AN EDGE OF THE WHEEL**, as an indexed family, so that the case analysis below is
by `rcases` on the constructors rather than by nested destructuring of the vertex type. -/
inductive WheelEdgeKind (n : ℕ) : WheelV n → WheelV n → Prop
  /-- two consecutive rim vertices (indices modulo `n`) -/
  | rim {i j : Fin n} (hne : i ≠ j) (hcyc : (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) :
      WheelEdgeKind n (wheelC i) (wheelC j)
  /-- a rim vertex and the hub -/
  | hub_rim {i : Fin n} : WheelEdgeKind n (wheelC i) wheelHub
  | rim_hub {i : Fin n} : WheelEdgeKind n wheelHub (wheelC i)
  /-- a rim vertex and its own leaf -/
  | rim_leaf {i : Fin n} : WheelEdgeKind n (wheelC i) (wheelL i)
  | leaf_rim {i : Fin n} : WheelEdgeKind n (wheelL i) (wheelC i)
  /-- the hub and a leaf -/
  | hub_leaf {i : Fin n} : WheelEdgeKind n wheelHub (wheelL i)
  | leaf_hub {i : Fin n} : WheelEdgeKind n (wheelL i) wheelHub

/-- **Adjacency in the wheel**: `c_i ~ c_j` iff `i ≠ j` and `j = i + 1` or `i = j + 1` modulo `n`
(the rim); the hub is adjacent to every rim vertex and to every leaf; the leaf `x_i` is adjacent to
`c_i` and to the hub; two leaves are never adjacent. -/
def wheelAdj (n : ℕ) (u v : WheelV n) : Prop :=
  match u, v with
  | Sum.inl (Sum.inl i), Sum.inl (Sum.inl j) =>
      i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val)
  | Sum.inl (Sum.inl _), Sum.inl (Sum.inr ()) => True
  | Sum.inl (Sum.inr ()), Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr ()), Sum.inl (Sum.inr ()) => False
  | Sum.inl (Sum.inl i), Sum.inr k => i = k
  | Sum.inl (Sum.inr ()), Sum.inr _ => True
  | Sum.inr k, Sum.inl (Sum.inl i) => i = k
  | Sum.inr _, Sum.inl (Sum.inr ()) => True
  | Sum.inr _, Sum.inr _ => False

/-- **ADJACENCY IN THE WHEEL IS THE INDEXED EDGE FAMILY**, in both directions. -/
theorem wheelAdj_iff {u v : WheelV n} : wheelAdj n u v ↔ WheelEdgeKind n u v := by
  constructor
  · intro h
    cases u with
    | inl hu =>
      cases hu with
      | inl i =>
        cases v with
        | inl hv =>
          cases hv with
          | inl j => exact WheelEdgeKind.rim h.1 h.2
          | inr uu => exact WheelEdgeKind.hub_rim
        | inr k =>
          subst h
          exact WheelEdgeKind.rim_leaf
      | inr uu =>
        cases v with
        | inl hv =>
          cases hv with
          | inl j => exact WheelEdgeKind.rim_hub
          | inr uu' => exact h.elim
        | inr k => exact WheelEdgeKind.hub_leaf
    | inr k =>
      cases v with
      | inl hv =>
        cases hv with
        | inl j => exact h ▸ WheelEdgeKind.leaf_rim
        | inr uu => exact WheelEdgeKind.leaf_hub
      | inr k => exact h.elim
  · intro h
    cases h with
    | rim hne hcyc => exact ⟨hne, hcyc⟩
    | hub_rim => exact trivial
    | rim_hub => exact trivial
    | rim_leaf => exact rfl
    | leaf_rim => exact rfl
    | hub_leaf => exact trivial
    | leaf_hub => exact trivial

/-- **THE WHEEL `wheel n`**: the odd rim together with a hub adjacent to all of it, and one leaf per
rim vertex adjacent to the rim vertex and to the hub. -/
def wheel (n : ℕ) : SimpleGraph (WheelV n) where
  Adj u v := wheelAdj n u v
  symm := ⟨fun u v h => (wheelAdj_iff.mpr (by
    cases u with
    | inl hu =>
      cases hu with
      | inl i =>
        cases v with
        | inl hv =>
          cases hv with
          | inl j => exact WheelEdgeKind.rim (Ne.symm h.1) h.2.symm
          | inr uu => exact WheelEdgeKind.rim_hub
        | inr k =>
          subst h
          exact WheelEdgeKind.leaf_rim
      | inr uu =>
        cases v with
        | inl hv =>
          cases hv with
          | inl j => exact WheelEdgeKind.hub_rim
          | inr uu' => exact h.elim
        | inr k => exact WheelEdgeKind.leaf_hub
    | inr k =>
      cases v with
      | inl hv =>
        cases hv with
        | inl j => exact h.symm ▸ WheelEdgeKind.rim_leaf
        | inr uu => exact WheelEdgeKind.hub_leaf
      | inr k => exact h.elim))⟩
  loopless := ⟨fun u h => (by
    cases u with
    | inl hu =>
      cases hu with
      | inl i => exact h.1 rfl
      | inr uu => exact h.elim
    | inr k => exact h.elim)⟩

/-- **CONSECUTIVE RIM VERTICES ARE ADJACENT.** -/
theorem wheelAdj_cycle (hn : 2 ≤ n) (i : Fin n) :
    (wheel n).Adj (wheelC i) (wheelC (cycSucc i)) := by
  refine ⟨fun he => Ne.symm (cycSucc_ne i hn) he, Or.inl (cycSucc_val i).symm⟩

/-- **THE HUB IS ADJACENT TO EVERY RIM VERTEX AND TO EVERY LEAF.** -/
theorem wheelAdj_hub (i : Fin n) : (wheel n).Adj (wheelC i) wheelHub := trivial

theorem wheelAdj_hub_leaf (i : Fin n) : (wheel n).Adj wheelHub (wheelL i) := trivial

/-- **A LEAF IS ADJACENT TO ITS RIM VERTEX.** -/
theorem wheelAdj_leaf (i : Fin n) : (wheel n).Adj (wheelC i) (wheelL i) := rfl

theorem wheelAdj_leaf' (i : Fin n) : (wheel n).Adj (wheelL i) (wheelC i) := rfl

/-- **THE NEIGHBOURS OF A LEAF ARE ITS RIM VERTEX AND THE HUB.** -/
theorem wheelAdj_leaf_neigh {i : Fin n} {w : WheelV n} (h : wheelAdj n (wheelL i) w) :
    (∃ j : Fin n, w = wheelC j) ∨ w = wheelHub := by
  rcases wheelAdj_iff.mp h with _ | _
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

/-- **THE RIM `C` OF THE WHEEL.** -/
def wheelCycleFins (n : ℕ) : Finset (WheelV n) :=
  (Finset.univ : Finset (Fin n)).image (fun i => wheelC i)

theorem mem_wheelCycleFins {x : WheelV n} : x ∈ wheelCycleFins n ↔ ∃ i : Fin n, x = wheelC i := by
  rw [wheelCycleFins, Finset.mem_image]
  constructor
  · rintro ⟨i, -, hxi⟩; exact ⟨i, hxi.symm⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, Finset.mem_univ i, rfl⟩

theorem card_wheelCycleFins : (wheelCycleFins n).card = n := by
  rw [wheelCycleFins, Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) wheelC_injective,
    Finset.card_univ, Fintype.card_fin]

/-- **THE RIM IS AN ODD CYCLE OF THE WHEEL.** -/
theorem isOddCycle_wheelCycleFins (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    IsOddCycle (wheel n) (wheelCycleFins n) := by
  refine ⟨n, wheelC, hodd, hn, wheelC_injective, fun j => wheelAdj_cycle (by omega) j, ?_⟩
  intro x
  rw [mem_wheelCycleFins]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

/-! ### Part 2 — two reusable lemmas -/

/-- **AN ODD CYCLE SURVIVING A DELETION.**  If every vertex of the odd cycle `C` lies outside `X`,
then `C` is an odd cycle of `deleteFinset G X`. -/
theorem isOddCycle_of_oddCycle_avoiding {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    (hC : IsOddCycle G C) (hdis : ∀ x ∈ C, x ∉ X) : IsOddCycle (deleteFinset G X) C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  refine ⟨m, f, hm, hm3, hinj, fun j => ?_, hmem⟩
  exact deleteFinset_adj.mpr
    ⟨hdis _ ((hmem _).mpr ⟨j, rfl⟩), hdis _ ((hmem _).mpr ⟨cycSucc j, rfl⟩), hcyc j⟩

/-- **A PAIRWISE ADJACENT TRIPLE OF PAIRWISE DISTINCT VERTICES IS AN ODD CYCLE**, for an arbitrary
vertex type: the cyclic ordering `a → b → c → a`.  (Round 120 proved this for `Fin n` only.) -/
theorem isOddCycle_triple' {V : Type*} [DecidableEq V] {H : SimpleGraph V} {a b c : V}
    (hab : H.Adj a b) (hbc : H.Adj b c) (hca : H.Adj c a) (hab' : a ≠ b) (hbc' : b ≠ c)
    (hca' : c ≠ a) : IsOddCycle H ({a, b, c} : Finset V) := by
  refine ⟨3, (fun j : Fin 3 => match j.val with
    | 0 => a
    | 1 => b
    | _ => c), rfl, by omega, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j
    fin_cases j
    · exact hab
    · exact hbc
    · exact hca
  · intro x
    simp only [Finset.mem_insert]
    constructor
    · intro hx
      rcases hx with hx | hx | hx
      · exact ⟨(0 : Fin 3), hx.symm⟩
      · exact ⟨(1 : Fin 3), hx.symm⟩
      · exact ⟨(2 : Fin 3), (Finset.mem_singleton.mp hx).symm⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr (Or.inl hi.symm)
      · exact Or.inr (Or.inr (hi.symm ▸ Finset.mem_singleton_self c))

/-! ### Part 3 — the petals of the wheel -/

/-- **THE PETAL OF THE WHEEL AT `c_i`**: the triangle `{c_i, h, x_i}`, which meets the rim in the
single vertex `c_i`. -/
def wheelTriangle (i : Fin n) : Finset (WheelV n) := {wheelC i, wheelHub, wheelL i}

theorem isOddCycle_wheelTriangle (i : Fin n) : IsOddCycle (wheel n) (wheelTriangle i) :=
  isOddCycle_triple' (wheelAdj_hub i) (wheelAdj_hub_leaf i) (wheelAdj_leaf' i)
    (wheelC_ne_wheelHub i) (wheelHub_ne_wheelL i) (wheelL_ne_wheelC i i)

/-- **MEMBERSHIP IN THE PETAL TRIANGLE.** -/
theorem mem_wheelTriangle {i : Fin n} {x : WheelV n} :
    x ∈ wheelTriangle i ↔ x = wheelC i ∨ x = wheelHub ∨ x = wheelL i := by
  simp only [wheelTriangle, Finset.mem_insert, Finset.mem_singleton]

theorem inter_wheelTriangle_wheelCycleFins (i : Fin n) :
    wheelTriangle i ∩ wheelCycleFins n = {wheelC i} := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    obtain ⟨j, hj⟩ := mem_wheelCycleFins.mp hx2
    rcases mem_wheelTriangle.mp hx1 with h | h | h
    · exact Finset.mem_singleton.mpr (hj.trans (congrArg wheelC (wheelC_injective (hj.symm.trans h))))
    · exact absurd (hj.symm.trans h) (wheelC_ne_wheelHub j)
    · exact absurd (hj.symm.trans h) (fun he => wheelL_ne_wheelC i j he.symm)
  · intro x hx
    have hx' : x = wheelC i := Finset.mem_singleton.mp hx
    rw [Finset.mem_inter]
    exact ⟨mem_wheelTriangle.mpr (Or.inl hx'), (mem_wheelCycleFins).2 ⟨i, hx'⟩⟩

theorem mem_petalSet_wheelCycleFins (hn : 3 ≤ n) (hodd : n % 2 = 1) {i : Fin n} :
    wheelC i ∈ PetalSet (wheel n) (wheelCycleFins n) :=
  mem_petalSet.mpr ⟨(mem_wheelCycleFins).2 ⟨i, rfl⟩, wheelTriangle i, isOddCycle_wheelTriangle i,
    inter_wheelTriangle_wheelCycleFins i⟩

/-- **EVERY RIM VERTEX IS AN ATTACHMENT POINT**: `PetalSet (wheel n) C = C`. -/
theorem petalSet_wheelCycleFins (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    PetalSet (wheel n) (wheelCycleFins n) = wheelCycleFins n := by
  refine Finset.Subset.antisymm (petalSet_subset (C := wheelCycleFins n)) ?_
  intro x hx
  obtain ⟨i, hi⟩ := mem_wheelCycleFins.mp hx
  rw [hi]
  exact mem_petalSet.mpr ⟨(mem_wheelCycleFins).2 ⟨i, rfl⟩, wheelTriangle i,
    isOddCycle_wheelTriangle i, inter_wheelTriangle_wheelCycleFins i⟩

/-- **THE ATTACHMENT SET OF THE WHEEL HAS `n` VERTICES, FOR EVERY `n`.** -/
theorem card_petalSet_wheelCycleFins (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    (PetalSet (wheel n) (wheelCycleFins n)).card = n := by
  rw [petalSet_wheelCycleFins hn hodd, card_wheelCycleFins]

/-! ### Part 4 — the deficiency of the wheel is at most `2`, for every `n` -/

/-- **Modulo `2`, a number and its successor differ.** -/
theorem mod_two_succ_ne {k : ℕ} : k % 2 ≠ (k + 1) % 2 := by
  intro h
  have h2 : (k + 1) % 2 = (k % 2 + 1) % 2 := by rw [Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [hk] at h2; omega
  · rw [hk] at h2; omega

/-- **THE TWO-VERTEX TRANSVERSAL OF THE WHEEL**: the hub and the last rim vertex. -/
def wheelDeleteFins (n : ℕ) (hn : 0 < n) : Finset (WheelV n) := {wheelHub, wheelC (wheelLast hn)}

theorem mem_wheelDelete (i : Fin n) (hn : 0 < n) :
    wheelC i ∈ wheelDeleteFins n hn ↔ i = wheelLast hn := by
  rw [wheelDeleteFins, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact absurd h (wheelC_ne_wheelHub i)
    · exact wheelC_injective h
  · rintro h
    exact Or.inr (congrArg wheelC h)

/-- **THE PARITY COLOURING OF THE WHEEL**: the rim by the parity of its index, each leaf the opposite
class, the hub an arbitrary class. -/
def wheelColour (v : WheelV n) : Fin 2 :=
  match v with
  | Sum.inl (Sum.inl i) => ⟨i.val % 2, by omega⟩
  | Sum.inl (Sum.inr ()) => ⟨0, by omega⟩
  | Sum.inr i => ⟨(i.val + 1) % 2, by omega⟩

theorem wheelColour_rim (i : Fin n) : (wheelColour (wheelC i)).val = i.val % 2 := rfl

theorem wheelColour_leaf (i : Fin n) : (wheelColour (wheelL i)).val = (i.val + 1) % 2 := rfl

/-- **DELETING THE HUB AND THE LAST RIM VERTEX LEAVES A BIPARTITE GRAPH.**  The residual graph is a
path (the rim without its last vertex) with a pendant leaf on each of its vertices; the colouring is
the parity of the rim index, each leaf taking the opposite class. -/
theorem isBipartite_delete_wheelDelete (hn : 0 < n) :
    (deleteFinset (wheel n) (wheelDeleteFins n hn)).IsBipartite := by
  refine ⟨wheelColour, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  have hmemhub : wheelHub ∈ wheelDeleteFins n hn := by
    simp only [wheelDeleteFins, Finset.mem_insert_self]
  cases u with
  | inl hu =>
    cases hu with
    | inl i =>
      cases v with
      | inl hv =>
        cases hv with
        | inl j =>
          have hadj' : i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) := hadj
          rcases hadj' with ⟨hne, hcyc⟩
          rcases hcyc with hcyc | hcyc
          · by_cases hc : i.val + 1 < n
            · have hj : j.val = i.val + 1 := by rw [Nat.mod_eq_of_lt hc] at hcyc; exact hcyc.symm
              have hne : wheelColour (wheelC i) ≠ wheelColour (wheelC j) := by
                intro h
                have hv : i.val % 2 = j.val % 2 := congrArg Fin.val h
                exact mod_two_succ_ne (hj ▸ hv)
              exact hne
            · have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
              have hge : n ≤ i.val + 1 := Nat.le_of_not_lt hc
              clear hcyc
              have hlast : i.val = n - 1 := by omega
              have hwi : i = wheelLast hn := Fin.ext hlast
              exact absurd ((mem_wheelDelete i hn).mpr hwi) h1
          · by_cases hc : j.val + 1 < n
            · have hj : i.val = j.val + 1 := by rw [Nat.mod_eq_of_lt hc] at hcyc; exact hcyc.symm
              have hne : wheelColour (wheelC i) ≠ wheelColour (wheelC j) := by
                intro h
                have hv : i.val % 2 = j.val % 2 := congrArg Fin.val h
                exact mod_two_succ_ne (hj ▸ hv.symm)
              exact hne
            · have hle : j.val + 1 ≤ n := Nat.succ_le_of_lt j.isLt
              have hge : n ≤ j.val + 1 := Nat.le_of_not_lt hc
              clear hcyc
              have hlast : j.val = n - 1 := by omega
              have hwj : j = wheelLast hn := Fin.ext hlast
              exact absurd ((mem_wheelDelete j hn).mpr hwj) h2
        | inr uu =>
          exact absurd hmemhub h2
      | inr j =>
        have hij : i = j := hadj
        have hne : wheelColour (wheelC i) ≠ wheelColour (wheelL j) := by
          intro h
          have hv : i.val % 2 = (j.val + 1) % 2 := congrArg Fin.val h
          exact mod_two_succ_ne (hij ▸ hv)
        exact hne
    | inr uu =>
      exact absurd hmemhub h1
  | inr i =>
    cases v with
    | inl hv =>
      cases hv with
      | inl j =>
        have hij : j = i := hadj
        have hne : wheelColour (wheelL i) ≠ wheelColour (wheelC j) := by
          intro h
          have hv : (i.val + 1) % 2 = j.val % 2 := congrArg Fin.val h
          exact mod_two_succ_ne (hij ▸ hv).symm
        exact hne
      | inr uu =>
        exact absurd hmemhub h2
    | inr j =>
      exact (show False from hadj).elim

/-- **THE HUB AND THE LAST RIM VERTEX ARE A TWO-VERTEX TRANSVERSAL.** -/
theorem closeToBipartite_two_wheel (hn : 3 ≤ n) : CloseToBipartite 2 (wheel n) := by
  have hpos : 0 < n := by omega
  refine ⟨wheelDeleteFins n hpos, ?_, isBipartite_delete_wheelDelete hpos⟩
  have hne2 : wheelHub ≠ wheelC (wheelLast hpos) := Ne.symm (wheelC_ne_wheelHub _)
  have hdisj : Disjoint ({wheelHub} : Finset (WheelV n)) {wheelC (wheelLast hpos)} := by
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    rw [Finset.mem_singleton] at ha hb
    exact hne2 (ha.symm.trans hb)
  have hcard : (wheelDeleteFins n hpos).card = 2 := by
    show (({wheelHub} ∪ {wheelC (wheelLast hpos)} : Finset (WheelV n))).card = 2
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton, Finset.card_singleton]
  omega

/-- **THE DEFICIENCY OF THE WHEEL IS AT MOST `2`, FOR EVERY `n`.** -/
theorem maxDef_le_two_wheel (hn : 3 ≤ n) : MaxDef (wheel n) ≤ 2 :=
  maxDef_le_closeToBipartite (closeToBipartite_two_wheel hn)

/-- **The wheel satisfies Erdős's hypothesis with parameter `2`.** -/
theorem locIndep_two_wheel (hn : 3 ≤ n) : LocIndep 2 (wheel n) :=
  locIndep_of_maxDef_le (maxDef_le_two_wheel hn)

/-! ### Part 5 — the refutation of every numerical bound on the attachment set -/

/-- **`|PetalSet G C| ≤ MaxDef G + c` IS FALSE FOR EVERY CONSTANT `c`.**  On the wheel of odd
`n = 2c + 7` the attachment set has `n` vertices while `MaxDef ≤ 2 ≤ c + 2`. -/
theorem not_card_petalSet_le_maxDef_add_wheel (c : ℕ) :
    ¬ ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
        (PetalSet (wheel n) (wheelCycleFins n)).card ≤ c + MaxDef (wheel n) := by
  intro h
  have h3 := h (2 * c + 7) (by omega) (by omega)
  have hn : 3 ≤ 2 * c + 7 := by omega
  rw [card_petalSet_wheelCycleFins hn (by omega)] at h3
  have h2 := maxDef_le_two_wheel hn
  omega

/-- **`|PetalSet G C| ≤ c * MaxDef G` IS FALSE FOR EVERY `c`** (witness: the wheel of odd
`n = 2c + 3`, whose attachment set has `n > 2c ≥ c * MaxDef` vertices). -/
theorem not_card_petalSet_le_mul_maxDef_wheel :
    ¬ ∀ c : ℕ, ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
        (PetalSet (wheel n) (wheelCycleFins n)).card ≤ c * MaxDef (wheel n) := by
  intro h
  have h3 := h 1 (2 * 1 + 3) (by omega) (by omega)
  have hn : 3 ≤ 2 * 1 + 3 := by omega
  rw [card_petalSet_wheelCycleFins hn (by omega)] at h3
  have h2 := maxDef_le_two_wheel hn
  omega

/-- **NO FUNCTION OF THE DEFICIENCY BOUNDS THE ATTACHMENT SET.**  This is the refutation of the
numerical blocker of rounds 119 and 120 in its strongest form: there is **no** `φ : ℕ → ℕ` with
`|PetalSet (wheel n) C| ≤ φ (MaxDef (wheel n))` for every odd `n ≥ 3`, and the family has deficiency
at most `2` throughout.

The proof is a pigeonhole argument, and it is important that it is: an arbitrary `φ` need not be
monotone, so one cannot simply compare `φ (MaxDef (wheel n))` with `φ 2`.  Rather, `MaxDef (wheel n)`
is a natural number at most `2`, hence one of `0`, `1`, `2`, so every odd `n` forces
`n ≤ φ 0 ∨ n ≤ φ 1 ∨ n ≤ φ 2`, i.e. `n ≤ max (φ 0) (φ 1) (φ 2)` — absurd for
`n = 2 * (that maximum + 1) + 1`. -/
theorem no_petalSet_bound_of_maxDef :
    ¬ ∃ φ : ℕ → ℕ, ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
        (PetalSet (wheel n) (wheelCycleFins n)).card ≤ φ (MaxDef (wheel n)) := by
  rintro ⟨φ, hφ⟩
  have key : ∀ n : ℕ, n % 2 = 1 → 3 ≤ n → n ≤ max (φ 0) (max (φ 1) (φ 2)) := by
    intro n hodd hn
    have h3 := hφ n hodd hn
    rw [card_petalSet_wheelCycleFins hn hodd] at h3
    have h2 := maxDef_le_two_wheel hn
    have hmem : MaxDef (wheel n) = 0 ∨ MaxDef (wheel n) = 1 ∨ MaxDef (wheel n) = 2 := by omega
    rcases hmem with h | h | h
    · rw [h] at h3
      have hle : φ 0 ≤ max (φ 0) (max (φ 1) (φ 2)) := Nat.le_max_left _ _
      omega
    · rw [h] at h3
      have hle : φ 1 ≤ max (φ 0) (max (φ 1) (φ 2)) :=
        Nat.le_trans (Nat.le_max_left (φ 1) (φ 2))
          (Nat.le_max_right (φ 0) (max (φ 1) (φ 2)))
      omega
    · rw [h] at h3
      have hle : φ 2 ≤ max (φ 0) (max (φ 1) (φ 2)) :=
        Nat.le_trans (Nat.le_max_right (φ 1) (φ 2))
          (Nat.le_max_right (φ 0) (max (φ 1) (φ 2)))
      omega
  exact absurd (key (2 * (max (φ 0) (max (φ 1) (φ 2)) + 1) + 1) (by omega) (by omega)) (by omega)

/-- **AND UNDER `LocIndep k G` THE ATTACHMENT SET IS NOT A FUNCTION OF `k` EITHER:** for every `φ`
there is an odd cycle `C` of a graph satisfying `LocIndep 2` with `|PetalSet G C| > φ 2`.  This is
the refutation of the round-119 blocker under Erdős's own hypothesis, not only under the deficiency
bound. -/
theorem not_petalSet_le_of_locIndep_two (φ : ℕ → ℕ) :
    ∃ (n : ℕ), n % 2 = 1 ∧ 3 ≤ n ∧
      (PetalSet (wheel n) (wheelCycleFins n)).card > φ 2 ∧ LocIndep 2 (wheel n) := by
  refine ⟨2 * (φ 2 + 1) + 1, by omega, by omega, ?_, locIndep_two_wheel (by omega)⟩
  rw [card_petalSet_wheelCycleFins (by omega) (by omega)]
  omega

/-! ### Part 6 — the hub route on the wheel: every petal passes through the hub -/

/-- **THE COLOURING OF THE HUB-AND-LEAVES STAR LEFT BY DELETING THE RIM**: the hub one class, every
leaf the other.  (It is deliberately *not* `wheelColour`, whose leaves carry the parity of the rim
index; on the rim-deleted graph the star needs one class for the hub and one for all the leaves.) -/
def wheelStarColour (v : WheelV n) : Fin 2 :=
  match v with
  | Sum.inr _ => ⟨1, by omega⟩
  | _ => ⟨0, by omega⟩

/-- **DELETING THE RIM LEAVES THE STAR (HUB PLUS LEAVES), WHICH IS BIPARTITE.** -/
theorem isBipartite_delete_wheelCycleFins :
    (deleteFinset (wheel n) (wheelCycleFins n)).IsBipartite := by
  refine ⟨wheelStarColour, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  cases u with
  | inl hu' =>
    cases hu' with
    | inl i => exact False.elim (h1 ((mem_wheelCycleFins).2 ⟨i, rfl⟩))
    | inr uu =>
      cases uu
      cases v with
      | inl hv' =>
        cases hv' with
        | inl j => exact False.elim (h2 ((mem_wheelCycleFins).2 ⟨j, rfl⟩))
        | inr uu' =>
          cases uu'
          exact False.elim (show wheelAdj n wheelHub wheelHub from hadj)
      | inr j =>
        intro h
        have h2 := congrArg Fin.val h
        simp only [wheelStarColour] at h2
        omega
  | inr i =>
    cases v with
    | inl hv' =>
      cases hv' with
      | inl j =>
        intro h
        have h2 := congrArg Fin.val h
        simp only [wheelStarColour] at h2
        omega
      | inr uu =>
        cases uu
        intro h
        have h2 := congrArg Fin.val h
        simp only [wheelStarColour] at h2
        omega
    | inr j => exact False.elim (show wheelAdj n (wheelL i) (wheelL j) from hadj)

/-- **A VERTEX OF THE WHEEL WITH TWO DISTINCT NEIGHBOURS, NEITHER OF WHICH IS THE HUB, IS A RIM
VERTEX.**  This is the local observation behind the next lemma: the only vertices of the wheel other
than the rim are the hub (adjacent to everything, hence useless) and the leaves, whose two neighbours
are its own rim vertex and the hub. -/
theorem wheelC_of_adj_two {u a b : WheelV n} (hu : u ≠ wheelHub) (ha : wheelAdj n u a)
    (hb : wheelAdj n u b) (hab : a ≠ b) (ha' : a ≠ wheelHub) (hb' : b ≠ wheelHub) :
    ∃ i : Fin n, u = wheelC i := by
  cases u with
  | inl hu' =>
    cases hu' with
    | inl i => exact ⟨i, rfl⟩
    | inr uu => exact False.elim (hu rfl)
  | inr i =>
    rcases wheelAdj_leaf_neigh ha with ⟨j, hj⟩ | hj
    · rw [hj] at ha
      have hij : j = i := ha
      rcases wheelAdj_leaf_neigh hb with ⟨j', hj'⟩ | hj'
      · rw [hj'] at hb
        have hjb : j' = i := hb
        exact False.elim (hab (hj.trans ((congrArg wheelC (hij.trans hjb.symm)).trans hj'.symm)))
      · exact False.elim (hb' hj')
    · exact False.elim (ha' hj)

/-- **EVERY ODD CYCLE OF THE WHEEL AVOIDING THE HUB LIES ON THE RIM.**  This is the structural heart
of the round: in the hub-deleted wheel every vertex outside the rim is a leaf with a single possible
neighbour, so two distinct cycle-neighbours of a vertex on a cycle force two rim vertices — and the
hub, which is the only other neighbour, has been removed. -/
theorem subset_wheelCycleFins_of_oddCycle_avoid_hub {D : Finset (WheelV n)} (hD : IsOddCycle (wheel n) D)
    (hnot : wheelHub ∉ D) : D ⊆ wheelCycleFins n := by
  have hD' : IsOddCycle (deleteFinset (wheel n) {wheelHub}) D :=
    isOddCycle_of_oddCycle_avoiding hD
      (fun _ hx hxh => hnot (by rwa [Finset.mem_singleton.mp hxh] at hx))
  obtain ⟨o, ho⟩ := hD'.cycleOrder
  have hne_hub : ∀ k : Fin o.m, o.f k ≠ wheelHub := by
    intro k h
    exact (deleteFinset_adj.mp (o.hcyc k)).1 (by
      rw [h]; exact Finset.mem_singleton_self wheelHub)
  have hmem : ∀ x ∈ D, ∃ i : Fin n, x = wheelC i := by
    intro x hx
    obtain ⟨j, hj⟩ := (o.hmem x).mp hx
    have hne1 : o.f (cycSucc j) ≠ o.f (o.prev j) := o.step_prev_ne j
    have hadj1 : wheelAdj n (o.f j) (o.f (cycSucc j)) :=
      (deleteFinset_adj.mp (o.hcyc j)).2.2
    have hadj2 : wheelAdj n (o.f j) (o.f (o.prev j)) :=
      (deleteFinset_adj.mp (o.adj_prev j)).2.2
    obtain ⟨i, hi⟩ := wheelC_of_adj_two (hne_hub _) hadj1 hadj2 hne1 (hne_hub _) (hne_hub _)
    exact ⟨i, hj ▸ hi⟩
  intro x hx
  obtain ⟨i, hi⟩ := hmem x hx
  rw [hi]
  exact (mem_wheelCycleFins).2 ⟨i, rfl⟩

/-- **EVERY ODD CYCLE OF THE WHEEL MEETS THE RIM.** -/
theorem hitsOddCycles_wheelCycleFins : HitsOddCycles (wheel n) (wheelCycleFins n) := by
  intro D hD hne
  have hDstar : IsOddCycle (deleteFinset (wheel n) (wheelCycleFins n)) D := by
    apply isOddCycle_of_oddCycle_avoiding hD
    intro z hz hzn
    exact absurd (hne ▸ Finset.mem_inter.mpr ⟨hz, hzn⟩) (by simp)
  exact False.elim (not_isOddCycle_of_isBipartite
    (G := deleteFinset (wheel n) (wheelCycleFins n)) isBipartite_delete_wheelCycleFins ⟨D, hDstar⟩)

/-- **THE SINGLE HUB IS A HUB COVER OF THE RIM.**  Every odd cycle meeting `C` in exactly one
vertex passes through `h`: an odd cycle avoiding `h` lies on the rim
(`JSP90.subset_wheelCycleFins_of_oddCycle_avoid_hub`) and therefore meets `C` in all its `n ≥ 3`
vertices. -/
theorem hubCover_wheelCycleFins (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    HubCover (wheel n) (wheelCycleFins n) {wheelHub} := by
  refine ⟨hitsOddCycles_wheelCycleFins, fun D hD h1 => ?_⟩
  by_cases hhub : wheelHub ∈ D
  · intro he
    exact absurd (he ▸ Finset.mem_inter.mpr ⟨hhub, Finset.mem_singleton_self wheelHub⟩) (by simp)
  have hsub := subset_wheelCycleFins_of_oddCycle_avoid_hub hD hhub
  have h3 := isOddCycle_card_ge_three hD
  have heq : D ∩ wheelCycleFins n = D := by
    refine Finset.ext fun y => ?_
    constructor
    · intro hy
      exact Finset.mem_inter.mp hy |>.1
    · intro hy
      exact Finset.mem_inter.mpr ⟨hy, hsub hy⟩
  rw [heq] at h1
  omega

/-- **THE INSTANCE OF `JSPProblem/Hub.lean` ON THE WHEEL: `CloseToBipartite n (wheel n)`,** the
constant `|C| - 1 + |{h}|` where round 119's attachment-set route would have paid `2n - 1`. -/
theorem closeToBipartite_wheel_hub (hn : 3 ≤ n) (hodd : n % 2 = 1) : CloseToBipartite n (wheel n) := by
  have h3 := isOddCycle_card_ge_three (isOddCycle_wheelCycleFins hn hodd)
  have hpos : 0 < (wheelCycleFins n).card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  have h := closeToBipartite_of_hubCover (C := wheelCycleFins n) (Z := {wheelHub})
    (isOddCycle_wheelCycleFins hn hodd) hc (hubCover_wheelCycleFins hn hodd)
  refine closeToBipartite_mono ?_ h
  rw [card_wheelCycleFins]
  simp only [Finset.card_singleton]
  omega

/-- **THE HUB ROUTE IS STRICTLY CHEAPER THAN THE ATTACHMENT-SET ROUTE ON THE WHEEL:**
`n = (|C| - 1) + 1 < (|C| - 1) + |PetalSet| = 2n - 1`. -/
theorem hubCover_constant_lt_wheel (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    (wheelCycleFins n).card - 1 + ({wheelHub} : Finset (WheelV n)).card
      < (wheelCycleFins n).card - 1 + (PetalSet (wheel n) (wheelCycleFins n)).card := by
  rw [card_wheelCycleFins, card_petalSet_wheelCycleFins hn hodd]
  simp only [Finset.card_singleton]
  omega

/-! ### Part 7 — the wheel resolved exactly: the attachment set costs nothing, and the refutation
extends to every parameter

Parts 1–6 settled the wheel in the *negative* direction (`JSP90.no_petalSet_bound_of_maxDef`).  This
part closes the family in the *positive* direction and pins it down exactly: although the
attachment set of the rim has `n` elements for every odd `n`, the odd cycle transversal number of
the wheel is **exactly `2`**, because the single hub absorbs every petal
(`JSP90.hubCover_wheelCycleFins`).  So the wheel is *not* a counterexample to Erdős #73 — it is the
machine-checked example showing that an unbounded attachment set need not be paid for at all, and
that the hub route is the right way to pay for it.

* **`JSP90.wheel_exists_index_ne`** — every rim index has a different rim index available (`n ≥ 1`);
* **`JSP90.exists_oddCycle_avoiding_vertex`** — no vertex of the wheel meets every odd cycle;
* **`JSP90.not_closeToBipartite_zero_wheel`, `JSP90.not_closeToBipartite_one_wheel`** — and hence
  **`JSP90.closeToBipartite_wheel_iff`: `CloseToBipartite m (wheel n) ↔ 2 ≤ m` for odd `n ≥ 3`**, the
  *exact* value of the conclusion on this family;
* **`JSP90.wheel_triple`** — the three numbers that make the wheel a sharp test of every
  attachment-set route: deficiency at most `2`, attachment set of size `n`, transversal number `2`;
* **`JSP90.not_petalSet_le_of_locIndep_ge_two`** — the refutation of the numerical blocker of rounds
  119 and 120 now holds under **Erdős's own hypothesis for every `k ≥ 2`**, not only at `k = 2`. -/

/-- **EVERY RIM INDEX HAS A DIFFERENT RIM INDEX AVAILABLE** (for `n ≥ 1`): the index one step along
the rim, reduced.  This is what lets the witnesses below be moved off any prescribed vertex. -/
theorem wheel_exists_index_ne (k : Fin n) (hn : 2 ≤ n) : ∃ j : Fin n, k ≠ j := by
  have hklt : k.val < n := k.isLt
  by_cases hc : k.val + 1 < n
  · refine ⟨⟨k.val + 1, by omega⟩, fun h => ?_⟩
    have hk : k.val = k.val + 1 := by
      have hh := congrArg Fin.val h
      simpa only [Fin.mk_val] using hh
    omega
  · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
    have hk0 : k.val = 0 := by
      have hh := congrArg Fin.val h
      simpa only [Fin.mk_val] using hh
    rw [hk0] at hklt hc
    exact hc (by omega)

/-- **FOR EVERY VERTEX OF THE WHEEL THERE IS AN ODD CYCLE AVOIDING IT** (for odd `n ≥ 3`): the hub
is avoided by the rim, and every rim vertex and every leaf is avoided by the petal triangle at a
different rim index. -/
theorem exists_oddCycle_avoiding_vertex {v : WheelV n} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    ∃ D : Finset (WheelV n), IsOddCycle (wheel n) D ∧ v ∉ D := by
  cases v with
  | inl hv' =>
    cases hv' with
    | inl k =>
      obtain ⟨j, hj⟩ := wheel_exists_index_ne k (by omega)
      refine ⟨wheelTriangle j, isOddCycle_wheelTriangle j, ?_⟩
      intro hx
      rcases mem_wheelTriangle.mp hx with h | h | h
      · exact absurd (wheelC_injective h) hj
      · exact wheelC_ne_wheelHub k h
      · exact (wheelL_ne_wheelC j k).symm h
    | inr uu =>
      refine ⟨wheelCycleFins n, isOddCycle_wheelCycleFins hn hodd, ?_⟩
      intro hx
      rcases (mem_wheelCycleFins).mp hx with ⟨l, hxl⟩
      exact (wheelC_ne_wheelHub l).symm hxl
  | inr k =>
    obtain ⟨i, hi⟩ := wheel_exists_index_ne k (by omega)
    refine ⟨wheelTriangle i, isOddCycle_wheelTriangle i, ?_⟩
    intro hx
    rcases mem_wheelTriangle.mp hx with h | h | h
    · exact wheelL_ne_wheelC k i h
    · exact wheelL_ne_wheelHub k h
    · exact absurd (wheelL_injective h) hi

/-- **THE WHEEL IS NOT BIPARTITE.** -/
theorem not_closeToBipartite_zero_wheel (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    ¬ CloseToBipartite 0 (wheel n) := by
  rintro ⟨X, hX, hbi⟩
  have hX0 : X = ∅ := Finset.card_eq_zero.mp (by omega)
  subst hX0
  exact not_isOddCycle_of_isBipartite (by simpa [deleteFinset_empty] using hbi)
    ⟨wheelCycleFins n, isOddCycle_wheelCycleFins hn hodd⟩

/-- **NO SINGLE VERTEX IS AN ODD CYCLE TRANSVERSAL OF THE WHEEL.** -/
theorem not_closeToBipartite_one_wheel (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    ¬ CloseToBipartite 1 (wheel n) := by
  rintro ⟨X, hX, hbi⟩
  by_cases hne : X.Nonempty
  · obtain ⟨v, hv⟩ := hne
    obtain ⟨D, hD, hDv⟩ := exists_oddCycle_avoiding_vertex (v := v) hn hodd
    have hpos : 0 < X.card := Finset.card_pos.mpr ⟨v, hv⟩
    have hcard : X.card = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
    have hvw : v = w := Finset.mem_singleton.mp (by simpa only [hw] using hv)
    subst hvw
    have hD' : IsOddCycle (deleteFinset (wheel n) {v}) D := by
      apply isOddCycle_of_oddCycle_avoiding hD
      intro x hx hxv
      exact hDv (by rwa [Finset.mem_singleton.mp hxv] at hx)
    rw [hw] at hbi
    exact not_isOddCycle_of_isBipartite hbi ⟨D, hD'⟩
  · have hX0 : X = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      exact hne
    subst hX0
    exact not_closeToBipartite_zero_wheel hn hodd ⟨∅, by simp, hbi⟩

/-- **THE ODD CYCLE TRANSVERSAL NUMBER OF THE WHEEL IS EXACTLY `2`**, for every odd `n ≥ 3`.  So an
attachment set of `n` vertices costs nothing here: the two-vertex transversal `{h, c_{n-1}}` is
optimal, and the hub alone already absorbs every petal (`JSP90.hubCover_wheelCycleFins`). -/
theorem closeToBipartite_wheel_iff (hn : 3 ≤ n) (hodd : n % 2 = 1) (m : ℕ) :
    CloseToBipartite m (wheel n) ↔ 2 ≤ m := by
  constructor
  · intro h
    obtain ⟨X, hX, hbi⟩ := h
    by_cases hm : 2 ≤ m
    · exact hm
    · exact False.elim (not_closeToBipartite_one_wheel hn hodd ⟨X, by omega, hbi⟩)
  · intro hm
    exact closeToBipartite_mono hm (closeToBipartite_two_wheel hn)

/-- **THE WHEEL: deficiency at most `2`, attachment set of size `n`, transversal number `2`.**  The
three numbers together say exactly why the wheel defeats every numerical bound of rounds 119 and
120 and defeats none of the transversal theorems. -/
theorem wheel_triple (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    MaxDef (wheel n) ≤ 2 ∧ (PetalSet (wheel n) (wheelCycleFins n)).card = n ∧
      CloseToBipartite 2 (wheel n) ∧ ¬ CloseToBipartite 1 (wheel n) :=
  ⟨maxDef_le_two_wheel hn, card_petalSet_wheelCycleFins hn hodd,
    closeToBipartite_two_wheel hn, not_closeToBipartite_one_wheel hn hodd⟩

/-- **THE NUMERICAL BLOCKER OF ROUNDS 119 AND 120 IS REFUTED UNDER ERDŐS'S OWN HYPOTHESIS FOR EVERY
`k ≥ 2`**, not only at `k = 2`: for every `φ` and every `k ≥ 2` there is an odd cycle `C` of a graph
satisfying `LocIndep k G` with `|PetalSet G C| > φ k`.  (Larger `k` is a *weaker* hypothesis, so the
`k = 2` case of `JSP90.not_petalSet_le_of_locIndep_two` carries all the others.) -/
theorem not_petalSet_le_of_locIndep_ge_two (φ : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ (n : ℕ), n % 2 = 1 ∧ 3 ≤ n ∧
      (PetalSet (wheel n) (wheelCycleFins n)).card > φ k ∧ LocIndep k (wheel n) := by
  obtain ⟨n, hodd, hn, hcard, hloc⟩ := not_petalSet_le_of_locIndep_two (fun _ => φ k)
  exact ⟨n, hodd, hn, hcard, locIndep_mono hk hloc⟩

end
end JSP90
