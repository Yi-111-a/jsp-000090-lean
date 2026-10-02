/-
# JSP-000090 — `JSPProblem/CPathSkip.lean`: **the shortest `C`-path is induced**, **a closed
`C`-path is an odd cycle**, and the **two-attachment cover**

Round 111 (`JSPProblem/CPath.lean`) introduced Mader's `C`-path and obtained from it the
two-attachment transversal `JSP90.closeToBipartite_of_twoAttach`: if an odd cycle `C` meets every
odd cycle of `G` in at least two vertices, then `G` is `|C| - 1`-close to bipartite.  Its
`discovery/JSP-000090/policy.json` named three concrete next lemmas, all of which are proved here:

1. `JSP90.IsCPath.skip` — **a chord of a `C`-path shortens it** (the splice `skipPath`);
2. `JSP90.IsCPath.Shortest` + `JSP90.IsCPath.induced_of_shortest` — **THE SHORTEST `C`-PATH IS
   INDUCED** (the policy lemma);
3. `JSP90.IsCPath.isOddCycle_return` — **a closed `C`-path of odd vertex-number is an odd cycle of
   `G`**, and `JSP90.oneAttach_of_isCPath_return` records that this odd cycle meets `C` in
   **exactly one vertex**.

## What is proved

| result | content |
| --- | --- |
| `skipPath`, `skip_len_lt`, `IsCPath.skip` | **A CHORD SHORTENS A `C`-PATH.**  A `C`-path of length `d` from `f i` to `x` with a chord `p a ~ p b`, `a + 2 ≤ b ≤ d`, gives a `C`-path of length `a + 1 + (d - b) < d` to the same target |
| **`IsCPath.Shortest`** | minimality of a `C`-path to `x` (necessarily a hypothesis: `Nat.find` needs a `DecidablePred`, and existence of a *function* is not decidable) |
| **`IsCPath.induced_of_shortest`** | **THE SHORTEST `C`-PATH IS INDUCED**: for `u ≠ v`, `u + 1 ≠ v`, `v + 1 ≠ u` one has `¬ G.Adj (p u) (p v)` |
| **`IsCPath.adj_target_of_shortest`** | Mader's neighbour count at the far end: in a shortest `C`-path the target `x` is adjacent only to the last two vertices of the path |
| **`IsCPath.isOddCycle_return`** | **A CLOSED `C`-PATH IS AN ODD CYCLE**: if `p d ~ p 0` and `d` is even, then `(univ).image p` is an odd cycle of `G` |
| **`oneAttach_of_isCPath_return`** | that odd cycle meets `C` in **exactly one vertex**, namely `f i`, and contains `x` — *Mader's one-attachment lemma in `C`-path form* |
| **`TwoAttachCover`, `closeToBipartite_of_twoAttachCover`** | **THE TWO-ATTACHMENT COVER.**  If `𝒞` is a family of **nonempty vertex sets** (not necessarily odd cycles) such that every odd cycle of `G` meets some member of `𝒞` in at least two vertices, then `CloseToBipartite (∑ X ∈ 𝒞, |X| - 1) G` — a **strict generalisation** of round 111 (singleton cover), and additive over the cover |
| **`erdos73On_of_twoAttachCover`** | **A NEW INSTANCE OF THE HEADLINE THEOREM**, with a constant **independent of `k`** |

## What is *not* proved

`jsp_000090_main` is still not declared and `JSP90.OddCycleErdosPosa r` is unchanged.  The
one-attachment lemma above says that a closed `C`-path produces an odd cycle meeting `C` once, but
it produces **no transversal**: the two-attachment *cover* hypothesis is what pays, and the
classical existence of such a cover for a 3-connected graph is the unresolved part.

## Toolchain notes

* `dite_eq_left` / `dite_eq_right` (Lean core; `dif_pos`/`dif_neg` are deprecated) reduce a `def`
  whose body is `if _h : c = true then … else …`; `skipPath_eq` / `skipPath_eq_tail` are the only
  places this is needed, and every later step rewrites with them instead of unfolding.
* `congrArg Fin.val` does **not** do what one expects here: its first argument is the function and
  its second the *pointwise* equality, so it returns `⟨↑u, _⟩ = ⟨↑v, _⟩`.  Use `rw [Fin.mk.injEq]`
  at that hypothesis instead — this is why `skipPath_val_inj` is stated on `.val`.
* `u.val` is **not** a syntactic subterm of `skipPath p hab hbd u`, so a `rw [← …] at h` fails to
  fire; rewrite forward (`rw [skipPath_eq …] at h`) — the pattern `skipPath p hab hbd u` does
  occur.
* After a `rw [skipPath_eq …]`, a `Fin` index is left as `↑⟨k, _⟩`; `simp only [Fin.val_mk]`
  normalises it so that `omega` and `h.adj_step` see through.
* `Finset.card_eq_one` is `#s = 1 ↔ ∃ a, s = {a}` — the convenient form for "an odd cycle meets `C`
  in exactly one vertex"; `Finset.card_eq_one_iff_existsUnique` is the membership form.
* `Finset.card_biUnion_le : #(s.biUnion t) ≤ ∑ a ∈ s, #(t a)` (in
  `Algebra/BigOperators/Group/Finset/Basic.lean`, not in `Data/Finset/Card.lean`) is the counting
  input of the cover theorem.
-/

import JSPProblem.CPath

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqCPathSkip : DecidableEq V := Classical.decEq V

/-! ### Part 1 — the shortcut path: a chord of a `C`-path shortens it -/

section Skip

variable {m d a b : ℕ}

/-- **THE SHORTCUT IS STRICTLY SHORTER**: `a + 1 + (d - b) < d` whenever `a + 2 ≤ b ≤ d`. -/
theorem skip_len_lt (hab : a + 2 ≤ b) (hbd : b ≤ d) : a + 1 + (d - b) < d := by omega

/-- The shortcut path has at most `d` vertices. -/
theorem skip_card_le (hab : a + 2 ≤ b) (hbd : b ≤ d) : a + 1 + (d - b) + 1 ≤ d := by omega

theorem skip_zero_idx (hab : a + 2 ≤ b) (hbd : b ≤ d) : 0 < a + 1 + (d - b) + 1 := by omega

theorem skip_last_idx (hab : a + 2 ≤ b) (hbd : b ≤ d) :
    a + 1 + (d - b) < a + 1 + (d - b) + 1 := by omega

/-- Every index of the shortcut path is an index of `p`. -/
theorem skip_idx_lt (hab : a + 2 ≤ b) (hbd : b ≤ d) {t : ℕ} (ht : t < a + 1 + (d - b) + 1) :
    t < d + 1 := by omega

/-- The tail index of the shortcut path is an index of `p`. -/
theorem skip_idx_tail (hab : a + 2 ≤ b) (hbd : b ≤ d) {t : ℕ} (ht : t < a + 1 + (d - b) + 1)
    (hnta : ¬ t ≤ a) : b + (t - a - 1) < d + 1 := by omega

/-- The tail index of the shortcut path is positive: it is at least `b`. -/
theorem skip_idx_tail_pos (hab : a + 2 ≤ b) (hbd : b ≤ d) {t : ℕ} (ht : t < a + 1 + (d - b) + 1)
    (hnta : ¬ t ≤ a) : 0 < b + (t - a - 1) := by omega

/-- The tail index of the shortcut path is strictly below `d`, so a step can be taken along it. -/
theorem skip_idx_tail_lt (hab : a + 2 ≤ b) (hbd : b ≤ d) {t : ℕ} (ht : t < a + 1 + (d - b))
    (hta : a < t) : b + (t - a - 1) < d := by omega

/-- The chord's first endpoint is an index of `p`. -/
theorem skip_idx_a (hab : a + 2 ≤ b) (hbd : b ≤ d) : a < d + 1 := by omega

/-- The chord's second endpoint is an index of `p`. -/
theorem skip_idx_b (hab : a + 2 ≤ b) (hbd : b ≤ d) : b < d + 1 := by omega

/-- **THE SHORTCUT PATH.**

`p 0 … p a`, then the chord `p a ~ p b`, then the tail `p b … p d`.  Index `a + 1 + s` is
`p (b + s)` for `s ≤ d - b`. -/
def skipPath (p : Fin (d + 1) → V) (hab : a + 2 ≤ b) (hbd : b ≤ d) :
    Fin (a + 1 + (d - b) + 1) → V :=
  fun t => if _h : t.val ≤ a then p ⟨t.val, skip_idx_lt hab hbd t.isLt⟩
            else p ⟨b + (t.val - a - 1), skip_idx_tail hab hbd t.isLt _h⟩

/-- From an equality of two `Fin` indices, their `.val`s are equal.  `congrArg Fin.val` does *not*
do this: it returns the equality of the indices, not of their values. -/
theorem val_of_eq {n : ℕ} {u v : Fin n} (h : u = v) : u.val = v.val := Fin.val_eq_of_eq h

/-- An index in the head of the shortcut path is the corresponding index of `p`. -/
theorem skipPath_eq (p : Fin (d + 1) → V) (hab : a + 2 ≤ b) (hbd : b ≤ d) (t : ℕ)
    (ht : t < a + 1 + (d - b) + 1) (hle : t ≤ a) :
    skipPath p hab hbd ⟨t, ht⟩ = p ⟨t, skip_idx_lt hab hbd ht⟩ := by
  simp only [skipPath, dite_eq_left hle]

/-- An index in the tail of the shortcut path is the corresponding index of `p`. -/
theorem skipPath_eq_tail (p : Fin (d + 1) → V) (hab : a + 2 ≤ b) (hbd : b ≤ d) (t : ℕ)
    (ht : t < a + 1 + (d - b) + 1) (hta : a < t) :
    skipPath p hab hbd ⟨t, ht⟩
      = p ⟨b + (t - a - 1), skip_idx_tail hab hbd ht (Nat.not_le.mpr hta)⟩ := by
  simp only [skipPath, dite_eq_right (Nat.not_le.mpr hta)]

/-- Every index of `p` is also an index of the shortcut path's ambient `Fin`. -/
theorem skip_idx_of (hab : a + 2 ≤ b) (hbd : b ≤ d) {t : ℕ} (ht : t < a + 1 + (d - b)) :
    t < a + 1 + (d - b) + 1 :=
  Nat.lt_trans ht (lt_d_succ _)

/-- **THE SHORTCUT PATH IS SIMPLE** whenever `p` is. -/
theorem skipPath_val_inj (p : Fin (d + 1) → V) (hab : a + 2 ≤ b) (hbd : b ≤ d)
    (hp : Function.Injective p) {u v : Fin (a + 1 + (d - b) + 1)}
    (huv : skipPath p hab hbd u = skipPath p hab hbd v) : u.val = v.val := by
  rcases em (u.val ≤ a) with hu | hu
  · by_cases hvv : (v.val : ℕ) ≤ a
    · simp only [Fin.val_mk, skipPath, dite_eq_left hu, dite_eq_left hvv] at huv
      have h5 := hp huv
      exact Fin.mk.inj_iff.mp h5
    · have h3 : u.val ≠ b + (v.val - a - 1) := by
        intro he
        have hz : 0 ≤ v.val - a - 1 := by omega
        have h4 : b ≤ b + (v.val - a - 1) := by omega
        omega
      simp only [Fin.val_mk, skipPath, dite_eq_left hu, dite_eq_right hvv] at huv
      have h5 := hp huv
      exact absurd (Fin.mk.inj_iff.mp h5) h3
  · by_cases hvv : (v.val : ℕ) ≤ a
    · have h3 : b + (u.val - a - 1) ≠ v.val := by
        intro he
        have hz : 0 ≤ u.val - a - 1 := by omega
        have h4 : b ≤ b + (u.val - a - 1) := by omega
        omega
      simp only [Fin.val_mk, skipPath, dite_eq_right hu, dite_eq_left hvv] at huv
      have h5 := hp huv
      exact absurd (Fin.mk.inj_iff.mp h5) h3
    · simp only [Fin.val_mk, skipPath, dite_eq_right hu, dite_eq_right hvv] at huv
      have h5 := hp huv
      have h2 := Fin.mk.inj_iff.mp h5
      omega

theorem skipPath_inj (p : Fin (d + 1) → V) (hab : a + 2 ≤ b) (hbd : b ≤ d)
    (hp : Function.Injective p) : Function.Injective (skipPath p hab hbd) := by
  intro u v huv
  exact Fin.ext (skipPath_val_inj p hab hbd hp huv)

variable {f : Fin m → V} {i : Fin m} {C : Finset V}
  {hCmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin m, f j = y} {x : V} {p : Fin (d + 1) → V}

/-- **A CHORD OF A `C`-PATH SHORTENS IT.**

If `p` is a `C`-path of length `d` from `f i` to `x`, and `p a` is adjacent to `p b` with
`a + 2 ≤ b ≤ d`, then the shortcut `p 0 … p a`, `p a ~ p b`, `p b … p d` is a `C`-path to the same
target `x` of length `a + 1 + (d - b)`, which is `< d` by `skip_len_lt`.

The two components that make the splice work are the chord itself and the tail indices, which
`skip_idx_tail_lt` keeps inside `p`. -/
theorem IsCPath.skip (h : IsCPath G m d f i C hCmem x p) (hab : a + 2 ≤ b) (hbd : b ≤ d)
    (hchord : G.Adj (p ⟨a, skip_idx_a hab hbd⟩) (p ⟨b, skip_idx_b hab hbd⟩)) :
    IsCPath G m (a + 1 + (d - b)) f i C hCmem x (skipPath p hab hbd) := by
  refine ⟨?_, ?_, h.notMem_end, skipPath_inj p hab hbd h.inj, ?_, ?_⟩
  · -- the start
    simp only [Fin.val_mk, skipPath, dite_eq_left (Nat.zero_le a)]
    exact h.start
  · -- the end
    have hnta : ¬ (a + 1 + (d - b) : ℕ) ≤ a := by omega
    have heq : b + ((a + 1 + (d - b)) - a - 1) = d := by omega
    simp only [Fin.val_mk, skipPath, dite_eq_right hnta, heq]
    exact h.end
  · -- no interior vertex lies on `C`
    intro j hj
    have hjlt : j.val < d + 1 := by omega
    by_cases hle : (j.val : ℕ) ≤ a
    · simp only [Fin.val_mk, skipPath, dite_eq_left hle]
      exact h.notMem_at j.val hjlt hj
    · have hlt : b + (j.val - a - 1) < d + 1 := by omega
      have hpos : 0 < b + (j.val - a - 1) := by omega
      simp only [Fin.val_mk, skipPath, dite_eq_right hle]
      exact h.notMem_at _ hlt hpos
  · -- the steps
    intro j
    rcases em (j.val + 1 ≤ a) with h1 | h1
    · have hja : j.val ≤ a := by omega
      have hjd : j.val < d := by omega
      simp only [Fin.val_mk, skipPath, dite_eq_left hja, dite_eq_left h1]
      exact h.adj_step j.val hjd
    · rcases em (j.val = a) with h2 | h2
      · have hja : j.val ≤ a := by omega
        have heq1 : (j.val + 1) - a - 1 = 0 := by omega
        have hja' : a ≤ a := Nat.le_refl a
        have hnb : ¬ (a + 1 : ℕ) ≤ a := by omega
        simp only [Fin.val_mk, skipPath, h2, heq1, show (a + 1) - a - 1 = 0 from by omega,
          Nat.add_zero, dite_eq_left hja', dite_eq_right hnb]
        exact hchord
      · have hn : ¬ (j.val : ℕ) ≤ a := by omega
        have hta : a < j.val := by omega
        have htail := skip_idx_tail_lt hab hbd j.isLt hta
        have heq1 : b + ((j.val + 1) - a - 1) = (b + (j.val - a - 1)) + 1 := by omega
        simp only [Fin.val_mk, skipPath, dite_eq_right hn, dite_eq_right h1, heq1]
        exact h.adj_step _ htail

/-- **THE SHORTCUT IS A `C`-PATH OF SMALLER LENGTH**, i.e. the length returned by `IsCPath.skip` is
strictly below `d`. -/
theorem IsCPath.skip_shorter (h : IsCPath G m d f i C hCmem x p) (hab : a + 2 ≤ b) (hbd : b ≤ d)
    (hchord : G.Adj (p ⟨a, skip_idx_a hab hbd⟩) (p ⟨b, skip_idx_b hab hbd⟩)) :
    a + 1 + (d - b) < d :=
  skip_len_lt hab hbd

end Skip

/-! ### Part 2 — minimality: **the shortest `C`-path is induced** -/

section Shortest

variable {m d : ℕ} {f : Fin m → V} {i : Fin m} {C : Finset V}
  {hCmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin m, f j = y} {x : V} {p : Fin (d + 1) → V}

/-- **A `C`-PATH FROM `f i` TO `x` IS SHORTEST** if no `C`-path from `f i` to `x` of smaller length
exists.

Minimality has to be a *hypothesis*: `Nat.find` would need a `DecidablePred` on the predicate, and
the predicate quantifies over a function `Fin (d' + 1) → V`, so it is not decidable. -/
def IsCPath.Shortest (G : SimpleGraph V) (m : ℕ) (d : ℕ) (f : Fin m → V) (i : Fin m) (C : Finset V)
    (hCmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin m, f j = y) (x : V) : Prop :=
  ∀ (d' : ℕ) (f' : Fin (d' + 1) → V), IsCPath G m d' f i C hCmem x f' → d ≤ d'

/-- **THE SHORTEST `C`-PATH IS INDUCED.**

No two vertices of a shortest `C`-path are adjacent unless they are consecutive along it (in either
order): any other chord would shortcut the path by `IsCPath.skip`, contradicting minimality.

This is the lemma named by `discovery/JSP-000090/policy.json` after round 111. -/
theorem IsCPath.induced_of_shortest (h : IsCPath G m d f i C hCmem x p)
    (hs : IsCPath.Shortest G m d f i C hCmem x) {u v : ℕ} (huv : u < d + 1) (hvv : v < d + 1)
    (hne : u ≠ v) (hnsucc : u + 1 ≠ v) (hpred : v + 1 ≠ u) :
    ¬ G.Adj (p ⟨u, huv⟩) (p ⟨v, hvv⟩) := by
  intro hchord
  by_cases hu : u + 2 ≤ v
  · have hbd : v ≤ d := by omega
    have hs' := hs _ _ (h.skip hu hbd hchord)
    omega
  · have hvlt : v + 2 ≤ u := by omega
    have hbd : u ≤ d := by omega
    have hs' := hs _ _ (h.skip hvlt hbd hchord.symm)
    omega

/-- **MADER'S NEIGHBOUR COUNT AT THE FAR END.**

In a shortest `C`-path the target `x = p d` is adjacent to `p u` only when `u = d` or `u + 1 = d`,
i.e. only to the last two vertices of the path. -/
theorem IsCPath.adj_target_of_shortest (h : IsCPath G m d f i C hCmem x p)
    (hs : IsCPath.Shortest G m d f i C hCmem x) {u : ℕ} (hu : u < d + 1)
    (hadj : G.Adj (p ⟨u, hu⟩) x) : u = d ∨ u + 1 = d := by
  by_contra hcon
  refine h.induced_of_shortest hs hu (lt_d_succ d) (by omega) (by omega) (by omega) ?_
  rw [← h.end] at hadj
  exact hadj

/-- **THE NEIGHBOUR COUNT ALONG A SHORTEST `C`-PATH.**

In a shortest `C`-path, a vertex `p j` of the path is adjacent to a vertex `p u` of the path only
when the two are consecutive along it: `u = j`, `u + 1 = j` or `j + 1 = u`.  Together with
`adj_target_of_shortest` (the case `j = d`, where the neighbour is the target `x` rather than a
vertex of the path) this is the complete local structure of a shortest `C`-path: **every vertex of a
shortest `C`-path has at most two neighbours on it, and they are its own two path-neighbours.** -/
theorem IsCPath.adj_iff_step_of_shortest (h : IsCPath G m d f i C hCmem x p)
    (hs : IsCPath.Shortest G m d f i C hCmem x) {u j : ℕ} (hu : u < d + 1) (hj : j < d + 1)
    (hadj : G.Adj (p ⟨u, hu⟩) (p ⟨j, hj⟩)) : u = j ∨ u + 1 = j ∨ j + 1 = u := by
  rcases em (j = d) with hjd | hjd
  · have hj' : (⟨j, hj⟩ : Fin (d + 1)) = ⟨d, lt_d_succ d⟩ := Fin.eq_of_val_eq hjd
    have hx : p ⟨j, hj⟩ = x := hj' ▸ h.end
    rcases h.adj_target_of_shortest hs hu (hx ▸ hadj) with h2 | h2
    · exact Or.inl (h2.trans hjd.symm)
    · exact Or.inr (Or.inl (h2.trans hjd.symm))
  · rcases em (u = j) with h1 | h1
    · exact Or.inl h1
    · rcases em (u + 1 = j) with h2 | h2
      · exact Or.inr (Or.inl h2)
      · rcases em (j + 1 = u) with h3 | h3
        · exact Or.inr (Or.inr h3)
        · exact (h.induced_of_shortest hs hu hj h1 h2 h3 hadj).elim

end Shortest

/-! ### Part 3 — the return: a closed `C`-path is an odd cycle of `G` -/

section Return

variable {m d : ℕ} {f : Fin m → V} {i : Fin m} {C : Finset V}
  {hCmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin m, f j = y} {x : V} {p : Fin (d + 1) → V}

/-- `cycSucc j` is the next index while `j.val < d`. -/
theorem cycSucc_eq_succ_of_lt {d : ℕ} {j : Fin (d + 1)} (hj : j.val < d) :
    cycSucc j = ⟨j.val + 1, Nat.succ_lt_succ hj⟩ := by
  apply Fin.ext
  show (j.val + 1) % (d + 1) = j.val + 1
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ hj)

/-- `cycSucc ⟨d⟩ = 0`. -/
theorem cycSucc_eq_zero_of_last {d : ℕ} :
    cycSucc ⟨d, lt_d_succ d⟩ = ⟨0, zero_lt_d_succ d⟩ := by
  apply Fin.ext
  show (d + 1) % (d + 1) = 0
  exact Nat.mod_self _

/-- **A CLOSED `C`-PATH IS AN ODD CYCLE OF `G`.**

If `p` is a `C`-path of length `d ≥ 2` from `f i` to `x ∉ C` and the target is adjacent to the
start, `p d ~ p 0`, then `(univ).image p` is an odd cycle of `G` — provided `d` is even, so that
the closed cycle has the odd number `d + 1` of vertices. -/
theorem IsCPath.isOddCycle_return [Fintype V] (h : IsCPath G m d f i C hCmem x p) (hd2 : 2 ≤ d)
    (hd : d % 2 = 0) (hclose : G.Adj (p ⟨d, lt_d_succ d⟩) (p ⟨0, zero_lt_d_succ d⟩)) :
    IsOddCycle G ((Finset.univ : Finset (Fin (d + 1))).image p) := by
  have hm : (d + 1) % 2 = 1 := by
    have h1 := Nat.mod_add_div d 2
    rw [hd, Nat.zero_add] at h1
    rw [← h1, Nat.add_comm (2 * (d / 2)) 1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hm3 : 3 ≤ d + 1 := by omega
  refine isOddCycle_image p hm hm3 h.inj ?_
  intro j
  by_cases hj : j.val < d
  · rw [cycSucc_eq_succ_of_lt hj]
    exact h.adj_step j.val hj
  · have hjlt := j.isLt
    have hjval : j.val = d := by omega
    have hj' : j = ⟨d, lt_d_succ d⟩ := Fin.ext hjval
    subst hj'
    rw [cycSucc_eq_zero_of_last]
    exact hclose

/-- **MADER'S ONE-ATTACHMENT LEMMA, IN `C`-PATH FORM.**

A closed `C`-path of even length gives an odd cycle `D` of `G` which **meets `C` in exactly one
vertex**, namely the start `f i`, and which contains the target `x`.  This is the first odd cycle
of `G` attached to `C` at a single point that this development constructs from a `C`-path. -/
theorem oneAttach_of_isCPath_return [Fintype V] (h : IsCPath G m d f i C hCmem x p) (hd2 : 2 ≤ d)
    (hd : d % 2 = 0) (hclose : G.Adj (p ⟨d, lt_d_succ d⟩) (p ⟨0, zero_lt_d_succ d⟩)) :
    let D := (Finset.univ : Finset (Fin (d + 1))).image p
    IsOddCycle G D ∧ (D ∩ C).card = 1 ∧ f i ∈ D ∧ x ∈ D := by
  dsimp only
  have hD : IsOddCycle G ((Finset.univ : Finset (Fin (d + 1))).image p) :=
    h.isOddCycle_return hd2 hd hclose
  have hfi : f i ∈ C := by
    rw [hCmem]
    exact ⟨i, rfl⟩
  have hfiD : f i ∈ (Finset.univ : Finset (Fin (d + 1))).image p :=
    Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, h.start⟩
  have hxD : x ∈ (Finset.univ : Finset (Fin (d + 1))).image p :=
    Finset.mem_image.mpr ⟨⟨d, lt_d_succ d⟩, Finset.mem_univ _, h.end⟩
  have hset : ((Finset.univ : Finset (Fin (d + 1))).image p) ∩ C = {f i} := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, -, hay⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).1
      have hyC : y ∈ C := (Finset.mem_inter.mp hy).2
      have h0 : a.val = 0 := by
        by_contra hne
        have hpos : 0 < a.val := Nat.pos_of_ne_zero hne
        have hmem : p ⟨a.val, a.isLt⟩ ∈ C := by
          rw [Fin.mk_val a]
          exact hay ▸ hyC
        exact absurd hmem (h.notMem_at a.val a.isLt hpos)
      have hae : a = ⟨0, by omega⟩ := Fin.eq_of_val_eq h0
      have hpa : p a = f i := hae ▸ h.start
      exact Finset.mem_singleton.mpr (hay.symm.trans hpa)
    · intro hy
      obtain rfl := Finset.mem_singleton.mp hy
      exact Finset.mem_inter.mpr ⟨hfiD, hfi⟩
  have hcard : ((Finset.univ : Finset (Fin (d + 1))).image p ∩ C).card = 1 := by
    rw [hset]
    simp
  exact ⟨hD, hcard, hfiD, hxD⟩

end Return

/-! ### Part 4 — the **two-attachment cover** -/

section Cover

variable {𝒞 : Finset (Finset V)}

/-- **`𝒞` IS A TWO-ATTACHMENT COVER OF `G`** if a vertex `pick X` is chosen in each of its (nonempty)
members and every odd cycle of `G` meets some member of `𝒞` in at least two vertices.

The members of `𝒞` need **not** be odd cycles: only their nonemptiness (to pick a vertex) and the
two-vertex attachment are used. -/
def TwoAttachCover (G : SimpleGraph V) (𝒞 : Finset (Finset V)) (pick : Finset V → V) : Prop :=
  (∀ X ∈ 𝒞, pick X ∈ X)
    ∧ (∀ D : Finset V, IsOddCycle G D → ∃ X ∈ 𝒞, 2 ≤ (D ∩ X).card)

/-- **AN ODD CYCLE MEETS `X` MINUS THE CHOSEN VERTEX.**

If `D` meets `X` in at least two vertices and `c ∈ X`, then `D` meets `X.erase c`: the single
vertex `c` accounts for at most one of the two, so a second one survives. -/
theorem exists_mem_inter_erase_of_card_ge_two {D X : Finset V} {c : V}
    (h2 : 2 ≤ (D ∩ X).card) : ∃ y ∈ D, y ∈ X.erase c := by
  have hne : ∃ y : V, y ∈ D ∩ X :=
    Finset.nonempty_iff_ne_empty.mpr (by
      intro hz
      rw [hz, Finset.card_empty] at h2
      omega)
  obtain ⟨y, hmemD⟩ := hne
  rw [Finset.mem_inter] at hmemD
  by_cases hyc : y = c
  · by_contra hcon
    push_neg at hcon
    have hsub : D ∩ X ⊆ ({c} : Finset V) := by
      intro z hz
      refine Finset.mem_singleton.mpr ?_
      by_contra hzc
      have hzX : z ∈ X := (Finset.mem_inter.mp hz).2
      have hz' : z ∉ X.erase c := hcon z (Finset.mem_inter.mp hz).1
      exact hz' (Finset.mem_erase.mpr ⟨hzc, hzX⟩)
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h3
    omega
  · exact ⟨y, hmemD.1, Finset.mem_erase.mpr ⟨hyc, hmemD.2⟩⟩

/-- **THE CERTIFICATE OF A TWO-ATTACHMENT COVER.**  The union of the sets `X \ {pick X}` over a
two-attachment cover meets every odd cycle of `G`; this is the explicit deletion set of
`closeToBipartite_of_twoAttachCover`. -/
theorem hitsOddCycles_of_twoAttachCover {𝒞 : Finset (Finset V)} {pick : Finset V → V}
    (hc : TwoAttachCover G 𝒞 pick) :
    HitsOddCycles G (𝒞.biUnion fun X => X.erase (pick X)) := by
  have hpick : ∀ X ∈ 𝒞, pick X ∈ X := hc.1
  have hatt : ∀ D : Finset V, IsOddCycle G D → ∃ X ∈ 𝒞, 2 ≤ (D ∩ X).card := hc.2
  intro D hD
  obtain ⟨X, hX, h2⟩ := hatt D hD
  obtain ⟨y, hyD, hyX⟩ := exists_mem_inter_erase_of_card_ge_two h2
  exact Finset.nonempty_iff_ne_empty.mp ⟨y, Finset.mem_inter.mpr ⟨hyD,
    (Finset.mem_biUnion (t := fun X => X.erase (pick X))).mpr
      ⟨X, hX, hyX⟩⟩⟩

/-- **THE COST OF A TWO-ATTACHMENT COVER**: the union of the sets `X \ {pick X}` has at most
`∑ X ∈ 𝒞, (|X| - 1)` elements. -/
theorem card_biUnion_erase_le_sum_card_sub_one_of_twoAttachCover {𝒞 : Finset (Finset V)}
    {pick : Finset V → V} (hc : TwoAttachCover G 𝒞 pick) :
    ((𝒞.biUnion fun X => X.erase (pick X)) : Finset V).card ≤ ∑ X ∈ 𝒞, (X.card - 1) := by
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun X hX => ?_)
  exact (Finset.card_erase_of_mem (hc.1 X hX)).le

/-- **THE TWO-ATTACHMENT COVER.**

If `𝒞` is a two-attachment cover of `G`, then `G` is the union of a bipartite graph and at most
`∑ X ∈ 𝒞, (|X| - 1)` vertices: for each `X ∈ 𝒞` delete `X` minus the chosen vertex `pick X`, and
the union of those sets meets every odd cycle of `G`.

This **strictly generalises** `JSP90.closeToBipartite_of_twoAttach`, which is the case
`𝒞 = {C}` with `C` an odd cycle (see `closeToBipartite_of_twoAttachCover_of_singleton` below). -/
theorem closeToBipartite_of_twoAttachCover [Fintype V] {pick : Finset V → V}
    (hc : TwoAttachCover G 𝒞 pick) :
    CloseToBipartite (∑ X ∈ 𝒞, (X.card - 1)) G := by
  have hpick : ∀ X ∈ 𝒞, pick X ∈ X := hc.1
  have hatt : ∀ D : Finset V, IsOddCycle G D → ∃ X ∈ 𝒞, 2 ≤ (D ∩ X).card := hc.2
  have hcount : ((𝒞.biUnion fun X => X.erase (pick X)) : Finset V).card
      ≤ ∑ X ∈ 𝒞, (X.card - 1) := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun X hX => ?_)
    exact (Finset.card_erase_of_mem (hpick X hX)).le
  refine ⟨𝒞.biUnion fun X => X.erase (pick X), hcount, ?_⟩
  exact isBipartite_delete_of_hitsOddCycles (hitsOddCycles_of_twoAttachCover hc)

/-- **ROUND 111'S THEOREM AS A COVER.**  A single odd cycle which every odd cycle meets in at least
two vertices is a two-attachment cover of size one, and the cover constant is exactly `|C| - 1`. -/
theorem closeToBipartite_of_twoAttachCover_of_singleton [Fintype V] {C : Finset V}
    (pick : V) (hpick : pick ∈ C) (hC : IsOddCycle G C)
    (hatt : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) :
    CloseToBipartite (C.card - 1) G := by
  have hc : TwoAttachCover G ({C} : Finset (Finset V)) (fun _ => pick) := by
    refine ⟨?_, ?_⟩
    · intro X hX
      have : X = C := by
        have : X ∈ ({C} : Finset (Finset V)) := hX
        simpa using this
      rw [this]
      exact hpick
    · intro D hD
      exact ⟨C, by simp, hatt D hD⟩
  have h := closeToBipartite_of_twoAttachCover (𝒞 := ({C} : Finset (Finset V))) hc
  rwa [show (∑ X ∈ ({C} : Finset (Finset V)), (X.card - 1)) = C.card - 1 by simp] at h

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: THE TWO-ATTACHMENT COVER CLASS.**

`LocIndep k G` together with a two-attachment cover `𝒞` gives
`CloseToBipartite (∑ X ∈ 𝒞, |X| - 1) G` — a constant **independent of `k`**, and a hypothesis far
weaker than "one odd cycle attracts every odd cycle twice": the cover may have many members and
none of them has to be an odd cycle. -/
theorem erdos73On_of_twoAttachCover [Fintype V] (k : ℕ) {𝒞 : Finset (Finset V)} (pick : Finset V → V)
    (hc : TwoAttachCover G 𝒞 pick) (_hG : LocIndep k G) :
    CloseToBipartite (∑ X ∈ 𝒞, (X.card - 1)) G :=
  closeToBipartite_of_twoAttachCover hc

/-- **THE TWO-ATTACHMENT COVER WITH A BOUNDED CONSTANT.**

If every member of the cover `𝒞` has at most `ℓ` vertices, the same transversal costs at most
`ℓ * |𝒞|` — so the cover theorem is *linear in the size of the cover*, which is the Erdős–Pósa shape
(one unit per member, as in `LocIndep.oddCycleFamily_card_le`). -/
theorem erdos73On_of_twoAttachCover_bounded [Fintype V] (k ℓ : ℕ) {𝒞 : Finset (Finset V)}
    (pick : Finset V → V) (hc : TwoAttachCover G 𝒞 pick) (_hG : LocIndep k G)
    (hb : ∀ X ∈ 𝒞, X.card ≤ ℓ) : CloseToBipartite (ℓ * 𝒞.card) G := by
  refine CloseToBipartite.mono (closeToBipartite_of_twoAttachCover hc) ?_
  have h1 : (∑ X ∈ 𝒞, (X.card - 1)) ≤ ∑ _X ∈ 𝒞, (ℓ - 1) :=
    Finset.sum_le_sum fun X hX => Nat.sub_le_sub_right (hb X hX) 1
  calc (∑ X ∈ 𝒞, (X.card - 1)) ≤ ∑ _X ∈ 𝒞, (ℓ - 1) := h1
    _ = (ℓ - 1) * 𝒞.card := by simp [Nat.mul_comm]
    _ ≤ ℓ * 𝒞.card := Nat.mul_le_mul_right 𝒞.card (Nat.sub_le ℓ 1)

/-- **THE COVER CONSTANT IS SUMED OVER THE MEMBERS OF THE COVER**, so a singleton cover of a cycle
`C` costs `|C| - 1` and the cover theorem is never weaker than round 111's. -/
theorem sum_card_sub_one_singleton (C : Finset V) :
    (∑ X ∈ ({C} : Finset (Finset V)), (X.card - 1)) = C.card - 1 := by
  simp

end Cover

end

end JSP90