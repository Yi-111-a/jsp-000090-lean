/-
# JSP-000090 — the RING LEMMA: in a graph whose odd cycles are *linear* there is no ring

Attack family 29 (round 82).  New module, imported from the root module `JSPProblem.lean`.

## What is proved

`JSPProblem/Cactus.lean` (round 81) introduced the class

```lean
JSP90.OddCactus G = LinearOddCycles G ∧ TwoHellyOddCycles G
```

and stated, but did **not** assume, the remaining implication `LinearOddCycles G → LinearRing G`
(Part 5 of that file): **three pairwise meeting odd cycles of a linear graph have a common
vertex**.  This file *proves* it, and round 81's two instances of the headline theorem are thereby
restated under the strictly weaker hypothesis `LinearOddCycles G` alone.

## The mathematics

Let `C`, `D`, `E` be odd cycles of a linear graph, pairwise meeting.  Linearity makes each
pairwise intersection a *single* point, say `a ∈ C ∩ D`, `b ∈ D ∩ E`, `c ∈ E ∩ C`.  If two of
`a`, `b`, `c` agree, that vertex is a common vertex of the three cycles and there is nothing to
prove.  Otherwise `a`, `b`, `c` are distinct, and linearity gives `c ∉ D`, `b ∉ C`, `a ∉ E` — so
every **interior** vertex of an arc of `C` avoids `D` and `E`, and so on.

Now take, in each of the three cycles, the **odd** one of the two arcs between the two points lying
on it: `A₁` in `C` from `a` to `c`, `A₂` in `E` from `c` to `b`, `A₃` in `D` from `b` to `a`
(exactly one of the two arcs of an odd cycle between two vertices is odd — `JSP90.arc_parity`).
Each arc is a simple path lying on its cycle, its interior is disjoint from the other two cycles,
and the three arcs join head to tail:

```
a ──A₁──▶ c ──A₂──▶ b ──A₃──▶ a
```

so their concatenation is a **simple cycle of `d₁ + d₂ + d₃` vertices**, and `d₁`, `d₂`, `d₃` are
all odd, so the cycle is odd.  It contains `a` and `c`, two distinct vertices of `C`, and it
differs from `C` (it also contains `b`, which is not on `C`) — contradicting linearity. ∎

## The machinery, developed here from scratch

* `JSP90.arcOf`, `JSP90.arcRev` — an arc of a cycle as a *directed* path, and the same path
  traversed backwards.  Both are maps `ℕ → V` (the value at `t` is the vertex `t` steps along),
  which makes every later construction free of dependent `if`s.  The `arcRev` part removes a case
  analysis that cannot be avoided: the three arcs of a ring need **not** be oriented
  consistently (the three-sun of `JSPProblem/Sun.lean` is the smallest example), and the directed
  form of the odd arc (`JSP90.exists_oddPath`, which picks the odd direction and reverses if need
  be) absorbs this once and for all;
* `JSP90.exists_oddPath` — **between two distinct vertices of an odd cycle there is a simple path
  of odd length lying on the cycle**, with injectivity, consecutive adjacency and containment in
  the cycle;
* `JSP90.arcCat3`, `JSP90.arcCat3_inj`, `JSP90.arcCat3_adj`,
  **`JSP90.isOddCycle_of_ring3` — THE THREE-ARC CYCLE CONSTRUCTOR**: three directed paths which
  join head to tail cyclically, and whose value sets meet only in the joining vertices,
  concatenate to a simple cycle; if the three lengths are odd, the cycle is odd.  This is the
  "closing path" generalisation of `JSP90.arc_isOddCycle_of_notMem` of `JSPProblem/Chord.lean`
  (which closes an arc through a single *vertex*) that round 81 named as the missing tool;
* `JSP90.twoHelly_of_linearOddCycles` — **THE RING LEMMA**, so that
  `JSP90.OddCactus G ↔ JSP90.LinearOddCycles G` (`JSP90.oddCactus_iff_linear`): *the odd cycles of
  `G` form a cactus if and only if any two of them meet in at most one vertex*;
* `JSP90.closeToBipartite_one_of_linear_of_locIndep_one`, `JSP90.erdos73On_linear_one` and
  `JSP90.erdos73On_linear` — **round 81's two instances of the headline theorem restated with the
  strictly weaker hypothesis `LinearOddCycles G`**: the optimal constant `1` at `k = 1`, and
  `k * (k + 1)` at every `k`, for a *larger* class of graphs, with no bound on the odd girth, the
  degrees, the packing weight or the number of branch vertices.

## Verification before formalising

The ring lemma was checked computationally first (the discipline of rounds 78 and 80): for
**every** graph on `n ≤ 6` vertices (exhaustive, all `2^15` graphs) and every triple of odd cycles
meeting pairwise in three distinct vertices, some odd cycle of the graph contains two of the three
vertices.  No counterexample; the three-sun (six vertices) is the smallest configuration in which
a ring occurs, and it is indeed a ring of three triangles.
-/
import JSPProblem.Cactus

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqRing : DecidableEq V := Classical.decEq V

/-! ## Part 0 — an arc of a cycle as a *directed* path -/

/-- The arc which starts at `i` and runs around the cycle in the direction of `cycSucc`, as a map
on `ℕ`: `A t` is the vertex `t` steps after `i`.  (The values at `t > d` are irrelevant; the length
`d` is only used by the lemmas below.) -/
def arcOf {m : ℕ} (f : Fin m → V) (i : Fin m) (d : ℕ) : ℕ → V :=
  fun t => f ((cycSucc^[t] : Fin m → Fin m) i)

@[simp] theorem arcOf_zero {m : ℕ} (f : Fin m → V) (i : Fin m) (d : ℕ) : arcOf f i d 0 = f i := rfl

@[simp] theorem arcOf_last {m : ℕ} (f : Fin m → V) (i : Fin m) (d : ℕ) :
    arcOf f i d d = f ((cycSucc^[d] : Fin m → Fin m) i) := rfl

/-- **The arc does not repeat a vertex** (for `d < m`, the vertices are the ones `0, 1, …, d` steps
after `i`, and these are pairwise distinct around the cycle). -/
theorem arcOf_inj {m d : ℕ} (hdm : d < m) (f : Fin m → V) (hinj : Function.Injective f) (i : Fin m)
    (s t : ℕ) (hs : s ≤ d) (ht : t ≤ d) (hab : arcOf f i d s = arcOf f i d t) : s = t := by
  by_contra hne
  exact absurd (hinj hab) (cycSucc_pow_inj i (by omega) (by omega) hne)

/-- **Consecutive entries of the arc are adjacent.** -/
theorem arcOf_adj {m d : ℕ} (hdm : d < m) {f : Fin m → V}
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) (i : Fin m) (t : ℕ) (ht : t < d) :
    G.Adj (arcOf f i d t) (arcOf f i d (t + 1)) := by
  have h1 : ((cycSucc^[t + 1] : Fin m → Fin m) i)
      = cycSucc ((cycSucc^[t] : Fin m → Fin m) i) := cycSucc_succ_pow m i t
  simp only [arcOf, h1]
  exact hcyc _

/-- **The arc lies on the cycle.** -/
theorem arcOf_mem {m d : ℕ} (hdm : d < m) {C : Finset V} (f : Fin m → V)
    (hmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) (i : Fin m) (t : ℕ) (ht : t ≤ d) :
    arcOf f i d t ∈ C :=
  (hmem _).mpr ⟨(cycSucc^[t] : Fin m → Fin m) i, rfl⟩

/-- **The same arc, traversed backwards**: `A t` is the vertex `d - t` steps after `i`. -/
def arcRev {m d : ℕ} (f : Fin m → V) (i : Fin m) : ℕ → V :=
  fun t => f ((cycSucc^[d - t] : Fin m → Fin m) i)

@[simp] theorem arcRev_zero {m d : ℕ} (f : Fin m → V) (i : Fin m) :
    arcRev (d := d) f i 0 = f ((cycSucc^[d] : Fin m → Fin m) i) := rfl

@[simp] theorem arcRev_last {m d : ℕ} (f : Fin m → V) (i : Fin m) : arcRev (d := d) f i d = f i := by
  simp [arcRev]

/-- **The reversed arc does not repeat a vertex.** -/
theorem arcRev_inj {m d : ℕ} (hdm : d < m) (f : Fin m → V) (hinj : Function.Injective f) (i : Fin m)
    (s t : ℕ) (hs : s ≤ d) (ht : t ≤ d) (hab : arcRev (d := d) f i s = arcRev (d := d) f i t) :
    s = t := by
  have key : ∀ p q : ℕ, p < m → q < m →
      ((cycSucc^[p] : Fin m → Fin m) i = (cycSucc^[q] : Fin m → Fin m) i) → p = q := by
    intro p q hp hq h
    by_contra h'
    exact absurd h (cycSucc_pow_inj i hp hq h')
  have heq : d - s = d - t := key _ _ (by omega) (by omega) (hinj hab)
  have h1 : d - s + s = d := Nat.sub_add_cancel hs
  have h2 : d - t + t = d := Nat.sub_add_cancel ht
  omega

/-- **Consecutive entries of the reversed arc are adjacent** (`G.Adj` is symmetric, so a backwards
step is a forwards step on the cycle). -/
theorem arcRev_adj {m d : ℕ} (hdm : d < m) {f : Fin m → V}
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) (i : Fin m) (t : ℕ) (ht : t < d) :
    G.Adj (arcRev (d := d) f i t) (arcRev (d := d) f i (t + 1)) := by
  have h1 : (d - (t + 1) = (d - t) - 1) := by omega
  have h2 : ((cycSucc^[d - t] : Fin m → Fin m) i)
      = cycSucc ((cycSucc^[((d - t) - 1)] : Fin m → Fin m) i) := by
    have h := cycSucc_succ_pow m i (d - t - 1)
    rw [← h]
    congr 1
    omega
  simp only [arcRev]
  rw [h1, h2]
  exact (hcyc ((cycSucc^[((d - t) - 1)] : Fin m → Fin m) i)).symm

/-- **The reversed arc lies on the cycle.** -/
theorem arcRev_mem {m d : ℕ} (hdm : d < m) {C : Finset V} (f : Fin m → V)
    (hmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) (i : Fin m) (t : ℕ) (ht : t ≤ d) :
    arcRev (d := d) f i t ∈ C :=
  (hmem _).mpr ⟨(cycSucc^[d - t] : Fin m → Fin m) i, rfl⟩

/-- **THE ODD ARC, AS A PATH FROM `i` TO `j`.**

Between two *distinct* vertices of an odd cycle there is a simple path of **odd** length lying on
the cycle, with endpoints `f i` and `f j`.  This is `JSP90.arc_parity` (exactly one of the two
arcs between two vertices of an odd cycle is odd) together with the two possible orientations; the
statement produced is *directed*, so that the three arcs of a ring can be traversed head to tail
whatever their orientations are. -/
theorem exists_oddPath {m : ℕ} (hm : m % 2 = 1) {C : Finset V} (f : Fin m → V)
    (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {i j : Fin m} (hij : i ≠ j) :
    ∃ (d : ℕ) (A : ℕ → V),
      0 < d ∧ d < m ∧ d % 2 = 1 ∧ A 0 = f i ∧ A d = f j ∧
      (∀ s t, s ≤ d → t ≤ d → A s = A t → s = t) ∧ (∀ t, t ≤ d → A t ∈ C) ∧
      (∀ t, t < d → G.Adj (A t) (A (t + 1))) := by
  obtain ⟨d, h0d, hdm, hdij⟩ := exists_arc (hm := by omega) (i := i) (j := j) hij
  rcases arc_parity hm hij d hdm hdij with ho | ho
  · refine ⟨d, arcOf f i d, h0d, hdm, ho, rfl, ?_, arcOf_inj hdm f hinj i, ?_, ?_⟩
    · rw [arcOf, hdij]
    · intro t ht
      exact arcOf_mem hdm f hmem i t ht
    · intro t ht
      exact arcOf_adj hdm hcyc i t ht
  · have hrev : ((cycSucc^[m - d] : Fin m → Fin m) j = i) := arc_rev hdm hdij
    have hpos : 0 < m - d := by omega
    have hlt : m - d < m := by omega
    refine ⟨m - d, arcRev (d := m - d) f j, hpos, hlt, ho, ?_, ?_,
      arcRev_inj hlt f hinj j, ?_, ?_⟩
    · have hz : m - d - 0 = m - d := by omega
      simp only [arcRev, hz, hrev]
    · exact arcRev_last f j
    · intro t ht
      exact arcRev_mem hlt f hmem j t ht
    · intro t ht
      exact arcRev_adj hlt hcyc j t ht

/-! ## Part 1 — the three-arc cycle constructor -/

/-- **The concatenation of three arcs**, as a map on `ℕ`: entry `j` is `A₁ (j + 1)` for `j < d₁`,
then `A₂ (j - d₁ + 1)` for `d₁ ≤ j < d₁ + d₂`, then `A₃ (j - d₁ - d₂ + 1)` beyond.  The joining
vertices `A₂ 0 = A₁ d₁` and `A₃ 0 = A₂ d₂` are thus left out (each is the last entry of the
preceding block), and the third joining vertex `A₃ d₃ = A₁ 0` is the last entry; the three arcs
therefore concatenate to a *closed* sequence of exactly `d₁ + d₂ + d₃` entries. -/
def arcCat3 (A₁ A₂ A₃ : ℕ → V) (d₁ d₂ d₃ : ℕ) : ℕ → V :=
  fun j => if j < d₁ then A₁ (j + 1) else if j < d₁ + d₂ then A₂ (j - d₁ + 1)
    else A₃ (j - d₁ - d₂ + 1)

/-- **THE THREE-ARC CYCLE IS SIMPLE.**  Three directed paths `A₁`, `A₂`, `A₃` of lengths `d₁`, `d₂`,
`d₃`, each of which is simple and which join head to tail cyclically (`A₁ d₁ = A₂ 0`,
`A₂ d₂ = A₃ 0`, `A₃ d₃ = A₁ 0`) and meet only in the joining vertices, are still simple after
concatenation: `arcCat3 A₁ A₂ A₃ d₁ d₂ d₃` takes pairwise distinct values on `0, …, d₁+d₂+d₃-1`,
i.e. the three arcs concatenate to a simple closed sequence. -/
theorem arcCat3_inj {d₁ d₂ d₃ : ℕ} (hd1 : 0 < d₁) (hd2 : 0 < d₂) (hd3 : 0 < d₃)
    (A₁ A₂ A₃ : ℕ → V)
    (hi1 : ∀ s t, s ≤ d₁ → t ≤ d₁ → A₁ s = A₁ t → s = t)
    (hi2 : ∀ s t, s ≤ d₂ → t ≤ d₂ → A₂ s = A₂ t → s = t)
    (hi3 : ∀ s t, s ≤ d₃ → t ≤ d₃ → A₃ s = A₃ t → s = t)
    (hd12 : ∀ s t, s ≤ d₁ → t ≤ d₂ → A₁ s = A₂ t → (s = d₁ ∧ t = 0) ∨ (s = 0 ∧ t = d₂))
    (hd23 : ∀ s t, s ≤ d₂ → t ≤ d₃ → A₂ s = A₃ t → (s = d₂ ∧ t = 0) ∨ (s = 0 ∧ t = d₃))
    (hd31 : ∀ s t, s ≤ d₃ → t ≤ d₁ → A₃ s = A₁ t → (s = d₃ ∧ t = 0) ∨ (s = 0 ∧ t = d₁)) :
    ∀ j k, j < d₁ + d₂ + d₃ → k < d₁ + d₂ + d₃ →
      arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ j = arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ k → j = k := by
  intro j k hj hk heq
  by_cases h1j : j < d₁
  · by_cases h1k : k < d₁
    · have hval : A₁ (j + 1) = A₁ (k + 1) := by
        simpa only [arcCat3, if_pos h1j, if_pos h1k] using heq
      have := hi1 (j + 1) (k + 1) (by omega) (by omega) hval
      omega
    · by_cases h2k : k < d₁ + d₂
      · have hja : j + 1 ≤ d₁ := by omega
        have hkb : 1 ≤ k - d₁ + 1 := by omega
        have hke : k - d₁ + 1 ≤ d₂ := by omega
        have hval : A₁ (j + 1) = A₂ (k - d₁ + 1) := by
          simpa only [arcCat3, if_pos h1j, if_neg h1k, if_pos h2k] using heq
        rcases hd12 (j + 1) (k - d₁ + 1) hja hke hval with h' | h'
        · exact absurd h'.2 (by omega)
        · exact absurd h'.1 (by omega)
      · have hja : j + 1 ≤ d₁ := by omega
        have hkb : 1 ≤ k - d₁ - d₂ + 1 := by omega
        have hke : k - d₁ - d₂ + 1 ≤ d₃ := by omega
        have hval : A₁ (j + 1) = A₃ (k - d₁ - d₂ + 1) := by
          simpa only [arcCat3, if_pos h1j, if_neg h1k, if_neg h2k] using heq
        rcases hd31 (k - d₁ - d₂ + 1) (j + 1) hke hja hval.symm with h' | h'
        · exact absurd h'.2 (by omega)
        · exact absurd h'.1 (by omega)
  · by_cases h2j : j < d₁ + d₂
    · by_cases h1k : k < d₁
      · have hja : 1 ≤ j - d₁ + 1 := by omega
        have hje : j - d₁ + 1 ≤ d₂ := by omega
        have hkb : k + 1 ≤ d₁ := by omega
        have hval : A₁ (k + 1) = A₂ (j - d₁ + 1) := by
          simpa only [arcCat3, if_neg h1j, if_pos h2j, if_pos h1k] using heq.symm
        rcases hd12 (k + 1) (j - d₁ + 1) hkb hje hval with h' | h'
        · exact absurd h'.2 (by omega)
        · exact absurd h'.1 (by omega)
      · by_cases h2k : k < d₁ + d₂
        · have hval : A₂ (j - d₁ + 1) = A₂ (k - d₁ + 1) := by
            simpa only [arcCat3, if_neg h1j, if_pos h2j, if_neg h1k, if_pos h2k] using heq
          have := hi2 (j - d₁ + 1) (k - d₁ + 1) (by omega) (by omega) hval
          omega
        · have hja : 1 ≤ j - d₁ + 1 := by omega
          have hje : j - d₁ + 1 ≤ d₂ := by omega
          have hkb : 1 ≤ k - d₁ - d₂ + 1 := by omega
          have hke : k - d₁ - d₂ + 1 ≤ d₃ := by omega
          have hval : A₂ (j - d₁ + 1) = A₃ (k - d₁ - d₂ + 1) := by
            simpa only [arcCat3, if_neg h1j, if_pos h2j, if_neg h1k, if_neg h2k] using heq
          rcases hd23 (j - d₁ + 1) (k - d₁ - d₂ + 1) hje hke hval with h' | h'
          · exact absurd h'.2 (by omega)
          · exact absurd h'.1 (by omega)
    · by_cases h1k : k < d₁
      · have hja : 1 ≤ j - d₁ - d₂ + 1 := by omega
        have hje : j - d₁ - d₂ + 1 ≤ d₃ := by omega
        have hkb : k + 1 ≤ d₁ := by omega
        have hval : A₃ (j - d₁ - d₂ + 1) = A₁ (k + 1) := by
          simpa only [arcCat3, if_neg h1j, if_neg h2j, if_pos h1k] using heq
        rcases hd31 (j - d₁ - d₂ + 1) (k + 1) hje hkb hval with h' | h'
        · exact absurd h'.2 (by omega)
        · exact absurd h'.1 (by omega)
      · by_cases h2k : k < d₁ + d₂
        · have hkb : 1 ≤ k - d₁ + 1 := by omega
          have hke : k - d₁ + 1 ≤ d₂ := by omega
          have hja : 1 ≤ j - d₁ - d₂ + 1 := by omega
          have hje : j - d₁ - d₂ + 1 ≤ d₃ := by omega
          have hval : A₂ (k - d₁ + 1) = A₃ (j - d₁ - d₂ + 1) := by
            simpa only [arcCat3, if_neg h1j, if_neg h2j, if_neg h1k, if_pos h2k] using heq.symm
          rcases hd23 (k - d₁ + 1) (j - d₁ - d₂ + 1) hke hje hval with h' | h'
          · exact absurd h'.2 (by omega)
          · exact absurd h'.1 (by omega)
        · have hval : A₃ (j - d₁ - d₂ + 1) = A₃ (k - d₁ - d₂ + 1) := by
            simpa only [arcCat3, if_neg h1j, if_neg h2j, if_neg h1k, if_neg h2k] using heq
          have := hi3 (j - d₁ - d₂ + 1) (k - d₁ - d₂ + 1) (by omega) (by omega) hval
          omega

/-- **THE THREE-ARC CYCLE WALKS ALONG `G`.**  With the hypotheses of `JSP90.arcCat3_inj` plus the
three walks `Adj (Aᵢ t) (Aᵢ (t+1))` for `t < dᵢ` and the three joins, consecutive entries of the
concatenation are adjacent, and so are the last and the first. -/
theorem arcCat3_adj {d₁ d₂ d₃ : ℕ} (hd1 : 0 < d₁) (hd2 : 0 < d₂) (hd3 : 0 < d₃)
    (A₁ A₂ A₃ : ℕ → V)
    (ha1 : ∀ t, t < d₁ → G.Adj (A₁ t) (A₁ (t + 1)))
    (ha2 : ∀ t, t < d₂ → G.Adj (A₂ t) (A₂ (t + 1)))
    (ha3 : ∀ t, t < d₃ → G.Adj (A₃ t) (A₃ (t + 1)))
    (hj1 : A₁ d₁ = A₂ 0) (hj2 : A₂ d₂ = A₃ 0) (hj3 : A₃ d₃ = A₁ 0) :
    (∀ j, j + 1 < d₁ + d₂ + d₃ → G.Adj (arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ j)
      (arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ (j + 1)))
    ∧ G.Adj (arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ (d₁ + d₂ + d₃ - 1)) (arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ 0) := by
  constructor
  · intro j hj
    by_cases h1j : j < d₁
    · by_cases h2j : j + 1 < d₁
      · have hval := ha1 (j + 1) (by omega)
        simpa only [arcCat3, if_pos h1j, if_pos h2j] using hval
      · have hjv : j + 1 = d₁ := by omega
        have h2a : j + 1 < d₁ + d₂ := by omega
        have hkb : ¬(j + 1 < d₁) := by omega
        have heq : d₁ - d₁ + 1 = 1 := by omega
        rw [arcCat3, if_pos h1j, arcCat3, if_neg hkb, if_pos h2a, hjv, heq, hj1]
        exact ha2 0 hd2
    · by_cases h2j : j < d₁ + d₂
      · by_cases h2b : j + 1 < d₁ + d₂
        · have hkb : ¬(j + 1 < d₁) := by omega
          have heq : (j + 1) - d₁ + 1 = (j - d₁ + 1) + 1 := by omega
          have hval := ha2 (j - d₁ + 1) (by omega)
          simpa only [arcCat3, if_neg h1j, if_pos h2j, if_neg hkb, if_pos h2b, heq] using hval
        · have hjv : j = d₁ + d₂ - 1 := by omega
          have hjv' : j + 1 = d₁ + d₂ := by omega
          have heq1 : d₁ + d₂ - 1 - d₁ + 1 = d₂ := by omega
          have heq3 : (d₁ + d₂ - 1 + 1) - d₁ - d₂ + 1 = 1 := by omega
          rw [arcCat3, if_neg h1j, if_pos h2j, hjv, heq1]
          rw [arcCat3, if_neg (by omega : ¬(d₁ + d₂ - 1 + 1 < d₁)),
            if_neg (by omega : ¬(d₁ + d₂ - 1 + 1 < d₁ + d₂)), heq3, hj2]
          exact ha3 0 hd3
      · have hkb : ¬(j + 1 < d₁) := by omega
        have h2a : ¬(j + 1 < d₁ + d₂) := by omega
        have heq : (j + 1) - d₁ - d₂ + 1 = (j - d₁ - d₂ + 1) + 1 := by omega
        have hval := ha3 (j - d₁ - d₂ + 1) (by omega)
        simpa only [arcCat3, if_neg h1j, if_neg h2j, if_neg hkb, if_neg h2a, heq] using hval
  · have hbig : (d₁ + d₂) + d₃ - 1 = (d₁ + d₂) + (d₃ - 1) :=
      Nat.add_sub_assoc (show 1 ≤ d₃ by omega) _
    have h1 : ¬((d₁ + d₂) + d₃ - 1 < d₁) := by rw [hbig]; omega
    have h2 : ¬((d₁ + d₂) + d₃ - 1 < d₁ + d₂) := by rw [hbig]; omega
    have heq : ((d₁ + d₂) + d₃ - 1) - d₁ - d₂ + 1 = d₃ := by
      rw [Nat.add_sub_assoc (show 1 ≤ d₃ by omega) _, Nat.sub_sub, Nat.add_sub_cancel_left,
        Nat.sub_add_cancel hd3]
    rw [arcCat3, if_neg h1, if_neg h2, arcCat3, if_pos hd1]
    rw [heq, show 0 + 1 = 1 from rfl, hj3]
    exact ha1 0 hd1

/-- **THE THREE-ARC CYCLE CONSTRUCTOR.**

Three directed paths `A₁`, `A₂`, `A₃` of lengths `d₁`, `d₂`, `d₃`, each of which is simple and walks
along `G`, and which

* join **head to tail cyclically**: `A₁ d₁ = A₂ 0`, `A₂ d₂ = A₃ 0`, `A₃ d₃ = A₁ 0`;
* meet only in the joining vertices: the common values of `A₁` and `A₂` are `A₁ d₁ = A₂ 0` and
  `A₁ 0 = A₂ d₂`, and cyclically,

concatenate to a **simple cycle** of `d₁ + d₂ + d₃` vertices — and if the three lengths are odd, to
an **odd** cycle.  This is the "closing path" generalisation of `JSP90.arc_isOddCycle_of_notMem` of
`JSPProblem/Chord.lean` (which closes an arc through a single *vertex*) that a ring of three odd
cycles needs. -/
theorem isOddCycle_of_ring3 {d₁ d₂ d₃ : ℕ} (hd1 : 0 < d₁) (hd2 : 0 < d₂) (hd3 : 0 < d₃)
    (ho1 : d₁ % 2 = 1) (ho2 : d₂ % 2 = 1) (ho3 : d₃ % 2 = 1)
    (A₁ A₂ A₃ : ℕ → V)
    (hi1 : ∀ s t, s ≤ d₁ → t ≤ d₁ → A₁ s = A₁ t → s = t)
    (hi2 : ∀ s t, s ≤ d₂ → t ≤ d₂ → A₂ s = A₂ t → s = t)
    (hi3 : ∀ s t, s ≤ d₃ → t ≤ d₃ → A₃ s = A₃ t → s = t)
    (ha1 : ∀ t, t < d₁ → G.Adj (A₁ t) (A₁ (t + 1)))
    (ha2 : ∀ t, t < d₂ → G.Adj (A₂ t) (A₂ (t + 1)))
    (ha3 : ∀ t, t < d₃ → G.Adj (A₃ t) (A₃ (t + 1)))
    (hj1 : A₁ d₁ = A₂ 0) (hj2 : A₂ d₂ = A₃ 0) (hj3 : A₃ d₃ = A₁ 0)
    (hd12 : ∀ s t, s ≤ d₁ → t ≤ d₂ → A₁ s = A₂ t → (s = d₁ ∧ t = 0) ∨ (s = 0 ∧ t = d₂))
    (hd23 : ∀ s t, s ≤ d₂ → t ≤ d₃ → A₂ s = A₃ t → (s = d₂ ∧ t = 0) ∨ (s = 0 ∧ t = d₃))
    (hd31 : ∀ s t, s ≤ d₃ → t ≤ d₁ → A₃ s = A₁ t → (s = d₃ ∧ t = 0) ∨ (s = 0 ∧ t = d₁)) :
    IsOddCycle G ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
      (fun j : Fin (d₁ + d₂ + d₃) => arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ j.val)) := by
  have hmod : ((d₁ + d₂ + d₃) : ℕ) % 2 = 1 := by
    have h12 : (d₁ + d₂) % 2 = 0 := by
      have h := Nat.add_mod d₁ d₂ 2
      rwa [ho1, ho2, show (1 + 1) % 2 = 0 by decide] at h
    have h := Nat.add_mod (d₁ + d₂) d₃ 2
    rwa [h12, ho3, show (0 + 1) % 2 = 1 by decide] at h
  have hcard : 3 ≤ d₁ + d₂ + d₃ := by omega
  obtain ⟨hstep, hclose⟩ :=
    arcCat3_adj hd1 hd2 hd3 A₁ A₂ A₃ ha1 ha2 ha3 hj1 hj2 hj3
  have hinjF := arcCat3_inj hd1 hd2 hd3 A₁ A₂ A₃ hi1 hi2 hi3 hd12 hd23 hd31
  refine ⟨d₁ + d₂ + d₃, fun j : Fin (d₁ + d₂ + d₃) => arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ j.val,
    hmod, hcard, ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.ext (hinjF a.val b.val a.isLt b.isLt hab)
  · intro j
    have hcs : (cycSucc j).val = (j.val + 1) % (d₁ + d₂ + d₃) := cycSucc_val j
    by_cases hjlast : j.val + 1 = d₁ + d₂ + d₃
    · have h0 : (cycSucc j).val = 0 := by rw [hcs, hjlast, Nat.mod_self]
      have hjv : j.val = d₁ + d₂ + d₃ - 1 := by omega
      simp only [Fin.val_mk, h0, hjv]
      exact hclose
    · have hjlt : j.val + 1 < d₁ + d₂ + d₃ := by omega
      have h1 : (cycSucc j).val = j.val + 1 := by rw [hcs, Nat.mod_eq_of_lt hjlt]
      simp only [Fin.val_mk, h1]
      exact hstep j.val hjlt
  · intro y
    constructor
    · intro hy
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
      exact ⟨j, hj⟩
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-! ## Part 2 — the ring lemma -/

/-- **Membership in a triple intersection.** -/
theorem mem_inter3' {C D E : Finset V} {x : V} (hxC : x ∈ C) (hxD : x ∈ D) (hxE : x ∈ E) :
    x ∈ C ∩ D ∩ E :=
  Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxC, hxD⟩, hxE⟩

/-- **THE RING LEMMA.**

In a graph whose odd cycles are *linear* (`JSP90.LinearOddCycles G`), three pairwise meeting odd
cycles have a common vertex: there is **no ring** of three odd cycles.  Equivalently
`LinearOddCycles G → LinearRing G`, the statement that `JSPProblem/Cactus.lean` left open as a
`def`.

The proof.  Linearity makes each pairwise intersection a single vertex `a ∈ C ∩ D`, `b ∈ D ∩ E`,
`c ∈ E ∩ C`; if two of them agree there is nothing to prove, and if they are all distinct then
`a ∉ E`, `b ∉ C`, `c ∉ D`.  Take in each cycle the **odd** one of the two arcs between the two
points lying on it (`JSP90.exists_oddPath`): `A₁` in `C` from `a` to `c`, `A₂` in `E` from `c` to
`b`, `A₃` in `D` from `b` to `a`.  Their interiors are disjoint from the other two cycles, so
`JSP90.isOddCycle_of_ring3` concatenates them into a **simple odd cycle** of `d₁ + d₂ + d₃`
vertices; it contains the two distinct vertices `a`, `c` of `C` and also `b ∉ C`, so it is a
different odd cycle from `C` — contradicting linearity (`JSP90.not_linear_of_two_mem`). -/
theorem twoHelly_of_linearOddCycles (h : LinearOddCycles G) : TwoHellyOddCycles G := by
  classical
  intro C D E hC hD hE hCD hDE hEC
  by_cases h1 : C = D
  · obtain ⟨x, hx⟩ := nonempty_of_ne_empty hEC
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact ⟨x, mem_inter3' hx2 (h1 ▸ hx2) hx1⟩
  by_cases h2 : D = E
  · obtain ⟨x, hx⟩ := nonempty_of_ne_empty hCD
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact ⟨x, mem_inter3' hx1 hx2 (h2 ▸ hx2)⟩
  by_cases h3 : E = C
  · obtain ⟨x, hx⟩ := nonempty_of_ne_empty hDE
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact ⟨x, mem_inter3' (h3 ▸ hx2) hx1 hx2⟩
  -- the three pairwise intersections are single vertices
  obtain ⟨a, ha⟩ := nonempty_of_ne_empty hCD
  obtain ⟨b, hb⟩ := nonempty_of_ne_empty hDE
  obtain ⟨c, hc⟩ := nonempty_of_ne_empty hEC
  have hCD : C ∩ D = {a} := h.eq_singleton_of_mem hC hD h1 ha
  have hDE : D ∩ E = {b} := h.eq_singleton_of_mem hD hE h2 hb
  have hEC : E ∩ C = {c} := h.eq_singleton_of_mem hE hC h3 hc
  have haC : a ∈ C := (Finset.mem_inter.mp ha).1
  have haD : a ∈ D := (Finset.mem_inter.mp ha).2
  have hbD : b ∈ D := (Finset.mem_inter.mp hb).1
  have hbE : b ∈ E := (Finset.mem_inter.mp hb).2
  have hcE : c ∈ E := (Finset.mem_inter.mp hc).1
  have hcC : c ∈ C := (Finset.mem_inter.mp hc).2
  by_cases hab : a = b
  · exact ⟨a, mem_inter3' haC haD (hab ▸ hbE)⟩
  by_cases hac : a = c
  · exact ⟨a, mem_inter3' haC haD (hac ▸ hcE)⟩
  by_cases hbc : b = c
  · exact ⟨b, mem_inter3' (hbc ▸ hcC) hbD (hbc ▸ hcE)⟩
  -- each of the three points is avoided by the third cycle
  have haE : a ∉ E := by
    intro hae
    have hmem : a ∈ E ∩ C := Finset.mem_inter.mpr ⟨hae, haC⟩
    have hac' : a = c := eq_of_mem_inter_eq_singleton hEC hmem
    exact hac hac'
  have hbC : b ∉ C := by
    intro hbc'
    have hmem : b ∈ C ∩ D := Finset.mem_inter.mpr ⟨hbc', hbD⟩
    have hba : b = a := eq_of_mem_inter_eq_singleton hCD hmem
    exact hab hba.symm
  have hcD : c ∉ D := by
    intro hcd
    have hmem : c ∈ D ∩ E := Finset.mem_inter.mpr ⟨hcd, hcE⟩
    have hcb : c = b := eq_of_mem_inter_eq_singleton hDE hmem
    exact hbc hcb.symm
  -- the cyclic orderings, and the indices of the three points
  obtain ⟨oC, hoC⟩ := hC.cycleOrder
  obtain ⟨oE, hoE⟩ := hE.cycleOrder
  obtain ⟨oD, hoD⟩ := hD.cycleOrder
  obtain ⟨ia, hia⟩ := (oC.hmem a).mp haC
  obtain ⟨ic, hic⟩ := (oC.hmem c).mp hcC
  obtain ⟨ic', hic'⟩ := (oE.hmem c).mp hcE
  obtain ⟨ib, hib⟩ := (oE.hmem b).mp hbE
  obtain ⟨ib', hib'⟩ := (oD.hmem b).mp hbD
  obtain ⟨ia', hia'⟩ := (oD.hmem a).mp haD
  have hac' : ia ≠ ic := by
    intro h
    have h1 : oC.f ic = a := h ▸ hia
    exact hac (h1.symm.trans hic)
  obtain ⟨d₁, A₁, h1pos, h1lt, h1odd, h1a, h1c, h1inj, h1mem, h1adj⟩ :=
    exists_oddPath hoC oC.f oC.hinj oC.hcyc oC.hmem hac'
  have haC' : A₁ 0 = a := h1a.trans hia
  have hcC' : A₁ d₁ = c := h1c.trans hic
  have hbc' : ic' ≠ ib := by
    intro h
    have h1 : oE.f ib = c := h ▸ hic'
    exact hbc (h1.symm.trans hib).symm
  obtain ⟨d₂, A₂, h2pos, h2lt, h2odd, h2c, h2b, h2inj, h2mem, h2adj⟩ :=
    exists_oddPath hoE oE.f oE.hinj oE.hcyc oE.hmem hbc'
  have hcE' : A₂ 0 = c := h2c.trans hic'
  have hbE' : A₂ d₂ = b := h2b.trans hib
  have hab' : ib' ≠ ia' := by
    intro h
    have h1 : oD.f ia' = b := h ▸ hib'
    exact hab (h1.symm.trans hia').symm
  obtain ⟨d₃, A₃, h3pos, h3lt, h3odd, h3b, h3a, h3inj, h3mem, h3adj⟩ :=
    exists_oddPath hoD oD.f oD.hinj oD.hcyc oD.hmem hab'
  have hbD' : A₃ 0 = b := h3b.trans hib'
  have haD' : A₃ d₃ = a := h3a.trans hia'
  -- the three arcs meet only in the joining vertices
  have hd12 : ∀ s t, s ≤ d₁ → t ≤ d₂ → A₁ s = A₂ t → (s = d₁ ∧ t = 0) ∨ (s = 0 ∧ t = d₂) := by
    intro s t hs ht heq
    have hmem : A₁ s ∈ E ∩ C := Finset.mem_inter.mpr ⟨by rw [heq]; exact h2mem t ht, h1mem s hs⟩
    have hsc : A₁ s = c := eq_of_mem_inter_eq_singleton hEC hmem
    have hA : A₁ s = A₁ d₁ := hsc.trans hcC'.symm
    have hB : A₂ t = A₂ 0 := (heq.symm.trans hsc).trans hcE'.symm
    have hh1 : s = d₁ := h1inj s d₁ hs (by omega) hA
    have hh2 : t = 0 := h2inj t 0 ht (by omega) hB
    exact Or.inl ⟨hh1, hh2⟩
  have hd23 : ∀ s t, s ≤ d₂ → t ≤ d₃ → A₂ s = A₃ t → (s = d₂ ∧ t = 0) ∨ (s = 0 ∧ t = d₃) := by
    intro s t hs ht heq
    have hmem : A₂ s ∈ D ∩ E := Finset.mem_inter.mpr ⟨by rw [heq]; exact h3mem t ht, h2mem s hs⟩
    have hsb : A₂ s = b := eq_of_mem_inter_eq_singleton hDE hmem
    have hA : A₂ s = A₂ d₂ := hsb.trans hbE'.symm
    have hB : A₃ t = A₃ 0 := (heq.symm.trans hsb).trans hbD'.symm
    have hh1 : s = d₂ := h2inj s d₂ hs (by omega) hA
    have hh2 : t = 0 := h3inj t 0 ht (by omega) hB
    exact Or.inl ⟨hh1, hh2⟩
  have hd31 : ∀ s t, s ≤ d₃ → t ≤ d₁ → A₃ s = A₁ t → (s = d₃ ∧ t = 0) ∨ (s = 0 ∧ t = d₁) := by
    intro s t hs ht heq
    have hmem : A₃ s ∈ C ∩ D := Finset.mem_inter.mpr ⟨by rw [heq]; exact h1mem t ht, h3mem s hs⟩
    have hsa : A₃ s = a := eq_of_mem_inter_eq_singleton hCD hmem
    have hA : A₃ s = A₃ d₃ := hsa.trans haD'.symm
    have hB : A₁ t = A₁ 0 := (heq.symm.trans hsa).trans haC'.symm
    have hh1 : s = d₃ := h3inj s d₃ hs (by omega) hA
    have hh2 : t = 0 := h1inj t 0 ht (by omega) hB
    exact Or.inl ⟨hh1, hh2⟩
  -- the three-arc cycle: a new odd cycle meeting `C` in the two vertices `a`, `c`
  set F : ℕ → V := arcCat3 A₁ A₂ A₃ d₁ d₂ d₃ with hFdef
  have hjo1 : A₁ d₁ = A₂ 0 := hcC'.trans hcE'.symm
  have hjo2 : A₂ d₂ = A₃ 0 := hbE'.trans hbD'.symm
  have hjo3 : A₃ d₃ = A₁ 0 := haD'.trans haC'.symm
  have hD : IsOddCycle G ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
      (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) := by
    have h1 := isOddCycle_of_ring3 h1pos h2pos h3pos h1odd h2odd h3odd A₁ A₂ A₃
      h1inj h2inj h3inj h1adj h2adj h3adj hjo1 hjo2 hjo3 hd12 hd23 hd31
    rwa [← hFdef] at h1
  have hmemA : ∀ (j : ℕ) (hj : j < d₁ + d₂ + d₃), F j
      ∈ ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
          (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) :=
    fun j hj => Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
  have memOf (x : V) (j : ℕ) (hj : j < d₁ + d₂ + d₃) (hx : F j = x) :
      x ∈ ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
        (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) := by
    subst hx
    exact hmemA j hj
  have haD'' : a ∈ ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
      (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) := by
    refine memOf a (d₁ + d₂ + d₃ - 1) (by omega) ?_
    rw [hFdef, arcCat3, if_neg (by omega : ¬(d₁ + d₂ + d₃ - 1 < d₁)),
      if_neg (by omega : ¬(d₁ + d₂ + d₃ - 1 < d₁ + d₂))]
    have heq : (d₁ + d₂ + d₃ - 1) - d₁ - d₂ + 1 = d₃ := by
      rw [Nat.add_sub_assoc (show 1 ≤ d₃ by omega) _, Nat.sub_sub, Nat.add_sub_cancel_left,
        Nat.sub_add_cancel (show 0 < d₃ by omega)]
    rw [heq]
    exact haD'
  have hcD'' : c ∈ ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
      (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) := by
    refine memOf c (d₁ - 1) (by omega) ?_
    rw [hFdef, arcCat3, if_pos (by omega : (d₁ - 1 : ℕ) < d₁),
      show d₁ - 1 + 1 = d₁ by omega]
    exact hcC'
  have hbE'' : b ∈ ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
      (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) := by
    refine memOf b (d₁ + d₂ - 1) (by omega) ?_
    rw [hFdef, arcCat3, if_neg (by omega : ¬(d₁ + d₂ - 1 < d₁)),
      if_pos (by omega : (d₁ + d₂ - 1 : ℕ) < d₁ + d₂),
      show d₁ + d₂ - 1 - d₁ + 1 = d₂ by omega]
    exact hbE'
  have hne : ((Finset.univ : Finset (Fin (d₁ + d₂ + d₃))).image
      (fun j : Fin (d₁ + d₂ + d₃) => F j.val)) ≠ C := by
    intro heq
    have hbC' : b ∈ C := heq ▸ hbE''
    exact hbC hbC'
  exact (not_linear_of_two_mem h hC hD (Ne.symm hne) haC haD'' hcC hcD'' hac).elim

/-! ## Part 3 — the cactus class is *equivalent* to linearity, and the instances restated -/

/-- **LINEARITY IMPLIES THE RING LEMMA.**  In the notation of `JSPProblem/Cactus.lean`
(`JSP90.LinearRing`): three pairwise meeting odd cycles of a linear graph have a common vertex. -/
theorem linearRing_of_linear (h : LinearOddCycles G) : LinearRing G := by
  intro C D E hC hD hE hCD hDE hEC
  obtain ⟨v, hv⟩ := twoHelly_of_linearOddCycles h C D E hC hD hE hCD hDE hEC
  exact ne_empty_of_mem hv

/-- **THE ODD CYCLES OF `G` FORM A CACTUS IFF THEY ARE LINEAR.**

`JSPProblem/Cactus.lean` defined `JSP90.OddCactus G` as *linear and two-Helly* and could prove
only `OddCactus G → LinearOddCycles G`.  The ring lemma gives the converse, so the two-Helly
condition is a **consequence** of linearity and not an extra hypothesis: the odd cycles of a graph
form a cactus precisely when no two of them meet in more than one vertex. -/
theorem oddCactus_iff_linear (h : LinearOddCycles G) : OddCactus G :=
  ⟨h, twoHelly_of_linearOddCycles h⟩

/-- **`OddCactus G ↔ LinearOddCycles G`**: the class of round 81 is exactly the class of graphs
whose odd cycles are pairwise meeting in at most one vertex. -/
theorem oddCactus_iff_of_linear (h : LinearOddCycles G) : OddCactus G ↔ LinearOddCycles G :=
  ⟨fun hc => hc.1, fun h' => oddCactus_iff_linear h'⟩

/-- **TWO ODD CYCLES THAT MEET A COMMON ODD CYCLE AT *DIFFERENT* VERTICES ARE DISJOINT, UNDER
LINEARITY ALONE** — the structural lemma of round 81, now with the two-Helly condition derived.
This is `JSP90.disjoint_of_attach_ne` of `JSPProblem/Cactus.lean` in the form used below. -/
theorem disjoint_of_attach_ne_lin (hlin : LinearOddCycles G) (htwo : TwoHellyOddCycles G)
    {C D E : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hE : IsOddCycle G E)
    (hDC : D ≠ C) (hEC : E ≠ C) {a a' : V} (ha : a ∈ D ∩ C) (ha' : a' ∈ E ∩ C)
    (haa' : a ≠ a') : D ∩ E = ∅ := by
  classical
  by_contra hcon
  obtain ⟨b, hb⟩ := nonempty_of_ne_empty hcon
  have haC : a ∈ C := (Finset.mem_inter.mp ha).2
  have ha'E : a' ∈ E := (Finset.mem_inter.mp ha').1
  have hCD : C ∩ D = {a} := hlin.eq_singleton_of_mem hC hD (Ne.symm hDC) (mem_inter_comm' ha)
  have hCE : C ∩ E = {a'} := hlin.eq_singleton_of_mem hC hE (Ne.symm hEC) (mem_inter_comm' ha')
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
  obtain ⟨v, hv⟩ := htwo C D E hC hD hE hmeetCD hmeetDE hmeetEC
  exact absurd (nonempty_of_mem hv) (not_nonempty_of_eq_empty htri)

/-! ### The `k = 1` level, with the optimal constant `1` -/

/-- **IN A LINEAR GRAPH WITH `LocIndep 1`, ALL THE ODD CYCLES HAVE A COMMON VERTEX.**  This is
`JSP90.exists_commonVertex_oddCactus_of_locIndep_one` of `JSPProblem/Cactus.lean` with the two-Helly
condition replaced by the ring lemma. -/
theorem exists_commonVertex_of_linearRing_of_locIndep_one (hG : LocIndep 1 G)
    (hlin : LinearOddCycles G) (htwo : TwoHellyOddCycles G)
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
    have hPQ : P ∩ Q = {a} := hlin.eq_singleton_of_mem hP hQ hPQ ha
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
      obtain ⟨v, hv⟩ := htwo P Q X hP hQ hX hmeetPQ hmeetQX hmeetXP
      exact absurd (nonempty_of_mem hv) (not_nonempty_of_eq_empty htri)
    exact ⟨a, hall⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1` FOR *LINEAR* GRAPHS, WITH THE OPTIMAL
CONSTANT `1`.**  This is `JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one` of
`JSPProblem/Cactus.lean` with the strictly weaker hypothesis `LinearOddCycles G`: the two-Helly
condition is not needed.  The constant `1` is the smallest possible for a non-bipartite graph, and
there is no bound on the odd girth, the degrees, the packing weight or the number of branch
vertices. -/
theorem closeToBipartite_one_of_linear_of_locIndep_one (hG : LocIndep 1 G)
    (hlin : LinearOddCycles G) : CloseToBipartite 1 G := by
  classical
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨a, ha⟩ :=
      exists_commonVertex_of_linearRing_of_locIndep_one hG hlin (twoHelly_of_linearOddCycles hlin)
        hodd
    refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨{a}, by simp, fun D hD => ?_⟩
    exact ne_empty_of_mem (Finset.mem_inter.mpr ⟨ha D hD, Finset.mem_singleton.mpr rfl⟩)
  · refine (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨∅, by simp, fun D hD => ?_⟩
    exact absurd ⟨D, hD⟩ hodd

/-- **THE SAME INSTANCE IN `Erdős73On` FORM, FOR LINEAR GRAPHS.** -/
theorem erdos73On_linear_one :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → LinearOddCycles G →
      CloseToBipartite 1 G :=
  fun _ _ _ hG hlin => closeToBipartite_one_of_linear_of_locIndep_one hG hlin

/-! ### Every `k`: the constant `k * (k + 1)` -/

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM AT EVERY `k`, FOR *LINEAR* GRAPHS.**  This is
`JSP90.erdos73On_oddCactus` of `JSPProblem/Cactus.lean` with the weaker hypothesis
`LinearOddCycles G`; the constant is unchanged, `k * (k + 1)`, and still no bound on the odd
girth, the degrees, the packing weight or the number of branch vertices.  The proof is the
maximum-packing argument of round 81 with the two-Helly condition derived by the ring lemma. -/
theorem erdos73On_of_linear (k : ℕ) (hG : LocIndep k G) (hlin : LinearOddCycles G)
    (htwo : TwoHellyOddCycles G) : CloseToBipartite (k * (k + 1)) G := by
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
        hlin (gr a) i (h𝒟oddc i (gr a) ((hgrmem a ha).1)) hi (hgrne a ha)
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
        exact disjoint_of_attach_ne_lin hlin htwo (C := i) (D := gr a) (E := gr b) hi
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

/-- **THE INSTANCE WITH THE HYPOTHESIS `LinearOddCycles G` ITSELF.** -/
theorem erdos73On_linear (k : ℕ) (hG : LocIndep k G) (hlin : LinearOddCycles G) :
    CloseToBipartite (k * (k + 1)) G :=
  erdos73On_of_linear k hG hlin (twoHelly_of_linearOddCycles hlin)

end
end JSP90
