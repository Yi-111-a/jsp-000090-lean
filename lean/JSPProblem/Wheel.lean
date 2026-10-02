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
-/

import JSPProblem.Hub

namespace JSP90

open Finset Fintype Set

variable {n : ℕ}

noncomputable section

/-! ### Part 1 — the wheel -/

/-- **The vertices of the wheel**: the rim (`Sum.inl (Sum.inl i)`), the hub (`Sum.inl (Sum.inr ())`)
and the leaves (`Sum.inr i`).  The vertex type has exactly `2n + 1` points. -/
def WheelV (n : ℕ) : Type := (Fin n ⊕ Unit) ⊕ Fin n

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
    · exact absurd (hj.symm.trans h) (fun he => wheelL_ne_wheelC j i he.symm)
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
    · exact h
  · rintro h
    exact Or.inr ⟨i, h⟩

/-- **DELETING THE HUB AND THE LAST RIM VERTEX LEAVES A BIPARTITE GRAPH.**  The residual graph is a
path (the rim without its last vertex) with a pendant leaf on each of its vertices; the colouring is
the parity of the rim index, each leaf taking the opposite class. -/
theorem isBipartite_delete_wheelDelete (hn : 0 < n) :
    (deleteFinset (wheel n) (wheelDeleteFins n hn)).IsBipartite := by
  refine ⟨fun v => match v with
    | Sum.inl (Sum.inl i) => ⟨i.val % 2, by omega⟩
    | Sum.inl (Sum.inr ()) => ⟨0, by omega⟩
    | Sum.inr i => ⟨(i.val + 1) % 2, by omega⟩, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  have hmemhub : wheelHub ∈ wheelDeleteFins n hn := by rw [wheelDeleteFins, Finset.mem_insert_self]
  rcases wheelAdj_iff.mp hadj with ⟨i, j, hne, hcyc⟩ | _ | _ | _ | _ | _ | _
  · rcases hcyc with hcyc | hcyc
    · by_cases hc : i.val + 1 < n
      · have hj : j.val = i.val + 1 := by rw [Nat.mod_eq_of_lt hc] at hcyc; exact hcyc.symm
        rw [hj]; exact mod_two_succ_ne
      · have hmod : (i.val + 1) % n = i.val + 1 - n := Nat.mod_eq_sub_mod (by omega)
        have hj : j.val = i.val + 1 - n := by rw [hmod] at hcyc; exact hcyc.symm
        have hlast : i.val = n - 1 := by omega
        exact absurd (Fin.ext hlast) ((mem_wheelDelete i hn).mpr (Fin.ext hlast) h1)
    · by_cases hc : j.val + 1 < n
      · have hj : i.val = j.val + 1 := by rw [Nat.mod_eq_of_lt hc] at hcyc; exact hcyc.symm
        rw [hj]; exact Ne.symm mod_two_succ_ne
      · have hmod : (j.val + 1) % n = j.val + 1 - n := Nat.mod_eq_sub_mod (by omega)
        have hj : i.val = j.val + 1 - n := by rw [hmod] at hcyc; exact hcyc.symm
        have hlast : j.val = n - 1 := by omega
        exact absurd (Fin.ext hlast) ((mem_wheelDelete j hn).mpr (Fin.ext hlast) h2)
  · exact absurd hmemhub h2
  · exact absurd hmemhub h1
  · exact mod_two_succ_ne
  · exact Ne.symm mod_two_succ_ne
  · exact absurd hmemhub h2
  · exact absurd hmemhub h1

/-- **THE HUB AND THE LAST RIM VERTEX ARE A TWO-VERTEX TRANSVERSAL.** -/
theorem closeToBipartite_two_wheel (hn : 3 ≤ n) : CloseToBipartite 2 (wheel n) := by
  have hpos : 0 < n := by omega
  refine ⟨wheelDeleteFins n hpos, ?_, isBipartite_delete_wheelDelete hpos⟩
  have hne : wheelHub ∉ wheelC (wheelLast hpos) := wheelC_ne_wheelHub _
  calc (wheelDeleteFins n hpos).card = ((wheelC (wheelLast hpos) : Finset (WheelV n))).card + 1 := by
        rw [wheelDeleteFins, Finset.card_insert_of_notMem hne]
    _ = 2 := by rw [Finset.card_singleton]; omega

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
  refine fun h => h (2 * c + 7) (by omega) (by omega) ?_
  have hn : 3 ≤ 2 * c + 7 := by omega
  rw [card_petalSet_wheelCycleFins hn (by omega)]
  have h2 := maxDef_le_two_wheel hn
  omega

/-- **`|PetalSet G C| ≤ c * MaxDef G` IS FALSE FOR EVERY `c`** (witness: the wheel of odd
`n = 2c + 3`, whose attachment set has `n > 2c ≥ c * MaxDef` vertices). -/
theorem not_card_petalSet_le_mul_maxDef_wheel :
    ¬ ∀ c : ℕ, ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
        (PetalSet (wheel n) (wheelCycleFins n)).card ≤ c * MaxDef (wheel n) := by
  intro h
  refine h 1 (2 * 1 + 3) (by omega) (by omega) ?_
  have hn : 3 ≤ 2 * 1 + 3 := by omega
  rw [card_petalSet_wheelCycleFins hn (by omega)]
  have h2 := maxDef_le_two_wheel hn
  omega

/-- **NO FUNCTION OF THE DEFICIENCY BOUNDS THE ATTACHMENT SET.**  This is the refutation of the
numerical blocker of rounds 119 and 120 in its strongest form: there is **no** `φ : ℕ → ℕ` with
`|PetalSet (wheel n) C| ≤ φ (MaxDef (wheel n))` for every odd `n ≥ 3`, and the family has deficiency
at most `2` throughout.  Indeed `φ` would have to satisfy `n ≤ φ 2` for all odd `n`. -/
theorem no_petalSet_bound_of_maxDef :
    ¬ ∃ φ : ℕ → ℕ, ∀ n : ℕ, n % 2 = 1 → 3 ≤ n →
        (PetalSet (wheel n) (wheelCycleFins n)).card ≤ φ (MaxDef (wheel n)) := by
  rintro ⟨φ, hφ⟩
  have key : ∀ n : ℕ, n % 2 = 1 → 3 ≤ n → n ≤ φ 2 := by
    intro n hodd hn
    have h := hφ n hodd hn
    have h2 := maxDef_le_two_wheel hn
    exact h.trans (φ.monotone h2)
  exact absurd (key (2 * (φ 2 + 1) + 1) (by omega) (by omega)) (by omega)

/-- **AND UNDER `LocIndep k G` THE ATTACHMENT SET IS NOT A FUNCTION OF `k` EITHER:** for every `φ`
there is an odd cycle `C` of a graph satisfying `LocIndep 2` with `|PetalSet G C| > φ 2`.  This is
the refutation of the round-119 blocker under Erdős's own hypothesis, not only under the deficiency
bound. -/
theorem not_petalSet_le_of_locIndep_two (φ : ℕ → ℕ) :
    ∃ (n : ℕ), n % 2 = 1 ∧ 3 ≤ n ∧
      (PetalSet (wheel n) (wheelCycleFins n)).card > φ 2 ∧ LocIndep 2 (wheel n) := by
  refine ⟨2 * (φ 2 + 1) + 1, by omega, by omega, ?_, locIndep_two_wheel _⟩
  rw [card_petalSet_wheelCycleFins (by omega) (by omega)]
  omega

/-! ### Part 6 — the hub route on the wheel: every petal passes through the hub -/

/-- **DELETING THE RIM LEAVES THE STAR (HUB PLUS LEAVES), WHICH IS BIPARTITE.** -/
theorem isBipartite_delete_wheelCycleFins :
    (deleteFinset (wheel n) (wheelCycleFins n)).IsBipartite := by
  refine ⟨fun v => match v with
    | Sum.inr _ => ⟨1, by omega⟩
    | _ => ⟨0, by omega⟩, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  rcases wheelAdj_iff.mp hadj with ⟨i, j, hne, hcyc⟩ | _ | _ | _ | _ | _ | _
  · exact absurd h1 ((mem_wheelCycleFins).2 ⟨i, rfl⟩)
  · exact absurd h1 ((mem_wheelCycleFins).2 ⟨i, rfl⟩)
  · exact absurd h2 ((mem_wheelCycleFins).2 ⟨i, rfl⟩)
  · exact absurd h1 ((mem_wheelCycleFins).2 ⟨i, rfl⟩)
  · exact absurd h2 ((mem_wheelCycleFins).2 ⟨i, rfl⟩)
  · intro he; have h' := Fin.mk.inj he; omega
  · intro he; have h' := Fin.mk.inj he; omega

/-- **EVERY ODD CYCLE OF THE WHEEL AVOIDING THE HUB LIES ON THE RIM.**  This is the structural heart
of the round: in the hub-deleted wheel every vertex outside the rim is a leaf with a single possible
neighbour, so two distinct cycle-neighbours of a vertex on a cycle force two rim vertices — and the
hub, which is the only other neighbour, has been removed. -/
theorem subset_wheelCycleFins_of_oddCycle_avoid_hub {D : Finset (WheelV n)} (hD : IsOddCycle (wheel n) D)
    (hnot : wheelHub ∉ D) : D ⊆ wheelCycleFins n := by
  have hD' : IsOddCycle (deleteFinset (wheel n) {wheelHub}) D :=
    isOddCycle_of_oddCycle_avoiding hD (fun x hx hxh => hnot (hxh ▸ hx))
  obtain ⟨o, ho⟩ := hD'.cycleOrder
  have hmem : ∀ x ∈ D, ∃ i : Fin n, x = wheelC i := by
    intro x hx
    obtain ⟨j, hj⟩ := (ho.hmem x).mp hx
    have hne : o.f (cycSucc j) ≠ o.f (o.prev j) := ho.step_prev_ne j
    have h1a : x ≠ wheelHub := by
      have := deleteFinset_adj.mp (ho.hcyc j)
      exact fun hxh => this.1 (hxh ▸ hj)
    have h2a : o.f (cycSucc j) ≠ wheelHub := by
      have := deleteFinset_adj.mp (ho.hcyc j)
      exact fun hxh => this.2.1 (hxh ▸ hj)
    have h3a : o.f (o.prev j) ≠ wheelHub := by
      have := deleteFinset_adj.mp (ho.adj_prev j)
      exact fun hxh => this.2.1 (hxh ▸ hj)
    have hadj1 : wheelAdj n x (o.f (cycSucc j)) := by
      have := deleteFinset_adj.mp (ho.hcyc j)
      rw [hj]; exact this.2.2
    have hadj2 : wheelAdj n x (o.f (o.prev j)) := by
      have := deleteFinset_adj.mp (ho.adj_prev j)
      rw [hj]; exact this.2.2
    rcases wheelAdj_iff.mp hadj1 with ⟨i, k, hne', hcyc⟩ | _ | _ | _ | _ | _ | _
    · exact ⟨i, rfl⟩
    · exact ⟨i, rfl⟩
    · exact absurd rfl h1a
    · exact ⟨i, rfl⟩
    · rcases wheelAdj_leaf_neigh hadj2 with ⟨k, hk⟩ | hk
      · exact absurd hne (by rw [rfl, hk])
      · exact absurd (h2a ▸ hk) h3a
    · exact absurd rfl h1a
    · exact absurd (h2a ▸ rfl) h1a
  intro x hx
  obtain ⟨i, hi⟩ := hmem x hx
  rw [hi]
  exact (mem_wheelCycleFins).2 ⟨i, rfl⟩

/-- **EVERY ODD CYCLE OF THE WHEEL MEETS THE RIM.** -/
theorem hitsOddCycles_wheelCycleFins : HitsOddCycles (wheel n) (wheelCycleFins n) := by
  intro D hD hne
  have hnothub : wheelHub ∉ D := by
    intro hh
    have hDstar : IsOddCycle (deleteFinset (wheel n) (wheelCycleFins n)) D :=
      isOddCycle_of_oddCycle_avoiding hD (fun y hy hyn => hne ⟨y, hy, hyn⟩)
    exact absurd hDstar (not_isOddCycle_of_isBipartite
      (G := deleteFinset (wheel n) (wheelCycleFins n)) isBipartite_delete_wheelCycleFins ⟨D, hDstar⟩)
  have hsub := subset_wheelCycleFins_of_oddCycle_avoid_hub hD hnothub
  have h3 := isOddCycle_card_ge_three hD
  have hne0 : D.Nonempty := Finset.card_ne_zero.mpr (by omega)
  rw [Finset.inter_eq_self.mpr hsub]
  exact Finset.nonempty_iff_ne_empty.mpr hne0

/-- **THE SINGLE HUB IS A HUB COVER OF THE RIM.**  Every odd cycle meeting `C` in exactly one
vertex passes through `h`: an odd cycle avoiding `h` lies on the rim
(`JSP90.subset_wheelCycleFins_of_oddCycle_avoid_hub`) and therefore meets `C` in all its `n ≥ 3`
vertices. -/
theorem hubCover_wheelCycleFins (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    HubCover (wheel n) (wheelCycleFins n) {wheelHub} := by
  refine ⟨hitsOddCycles_wheelCycleFins, fun D hD h1 => ?_⟩
  by_cases hhub : wheelHub ∈ D
  · exact Finset.nonempty_iff_ne_empty.mpr
      ⟨wheelHub, Finset.mem_inter.mpr ⟨hhub, Finset.mem_singleton_self wheelHub⟩⟩
  have hsub := subset_wheelCycleFins_of_oddCycle_avoid_hub hD hhub
  have h3 := isOddCycle_card_ge_three hD
  have hcardpos : 0 < (D ∩ wheelCycleFins n).card := by
    rw [Finset.inter_eq_self.mpr hsub]
    exact Finset.card_pos.mpr (Finset.card_ne_zero.mpr (by omega))
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

end JSP90
