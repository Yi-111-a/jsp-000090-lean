/-
# JSP-000090 — `JSPProblem/SplitSharp.lean`: the witness family of the split-graph axis
# (round 108)

Round 107 (`Split.lean`) proved the split-graph instance of Erdős #73,

```
JSP90.closeToBipartite_of_splitPartition   LocIndep k G → SplitPartition G A B → B.Nonempty
                                           → CloseToBipartite (k + 1) G
```

with the constant `k + 1`, and proved the constant optimal *within the class* in the conditional
sense (`closeToBipartite_split_iff`: `τ(G) ∈ {|B| − 1, |B| − 2}`, the second regime being
`IsolatedPair G A B`).  Its Part 4 named a graph on which the constant `k + 1` is attained and left
the `Finset` bookkeeping of the `LocIndep` proof undone.

**The graph analysed in `Split.lean` Part 4 was wrong, and this file replaces that analysis.**  The
graph named there — `K_{n,n}` with a perfect matching removed, sides `A = {(i, false)}`,
`B = {(i, true)}`, `(i, false) ~ (j, true) iff i ≠ j` — is *bipartite* (it is `C_6` at `n = 3`), so
`B` is not a clique and it is not a split graph at all.  The correct witness needs the clique side
to be a clique *as well*:

> **`splitWitness n`** on `Fin n × Bool`: `p ~ q` iff `p.1 ≠ q.1` and it is **not** the case that
> `p.2 = q.2 = false`.  I.e. `A = {(i, false)}` is independent, `B = {(i, true)}` is a clique, and
> the cross edge `a_i ~ b_j` is present exactly when `i ≠ j`.

This file builds that graph, proves it is a split graph, computes **both** sides of Erdős #73 on it
exactly, and concludes that the constant `k` is **not** sufficient: for every `k ≥ 1` there is a
finite graph satisfying `LocIndep k` which is **not** `k`-close to bipartite.

## What is proved

| result | content |
| --- | --- |
| `JSP90.splitWitness`, `swA`, `swB`, `mem_swA`, `mem_swB`, `card_swA`, `card_swB` | the graph and its two sides |
| `JSP90.splitWitness_splitPartition` | it is a split graph with `\|A\| = \|B\| = n` |
| `JSP90.not_isolatedPair_splitWitness` | no pair of the clique side is isolated (`3 ≤ n`) |
| `JSP90.locIndep_splitWitness` | **`LocIndep k (splitWitness (k + 2))`** — Erdős's hypothesis *holds*, so the witness is in range |
| `JSP90.indepCard_two`, `JSP90.maxDef_splitWitness` | **`MaxDef (splitWitness (k + 2)) = k`** — the *exact value* of the hypothesis: it is tight |
| `JSP90.closeToBipartite_splitWitness` | `CloseToBipartite (k + 1) (splitWitness (k + 2))` |
| `JSP90.not_closeToBipartite_splitWitness` | `¬ CloseToBipartite k (splitWitness (k + 2))` |
| **`JSP90.closeToBipartite_iff_splitWitness`** | **`CloseToBipartite m (splitWitness (k + 2)) ↔ k + 1 ≤ m`** |
| **`JSP90.not_erdos73On_splitWitness`** | **`¬ Erdős73On k k`** for `k ≥ 1`: **`f(k) ≥ k + 1`** |
| `JSP90.erdos73On_of_splitPartition_optimal` | the constant `k + 1` of round 107's split-graph instance is optimal |

`JSP90.not_erdos73On_splitWitness` is the first *lower* bound on the constant of Erdős #73 that is
strictly larger than the `f(k) ≥ k` of rounds 39/104, and it is a statement about the answer to the
problem itself, not only about a class.

## Why the independent set in the `LocIndep` proof is *not* "the independent side"

For `X ⊆ V`, with `a = |X ∩ A|`, `b = |X ∩ B|`, and index sets `I = (X ∩ A).image fst`,
`J = (X ∩ B).image fst`, the largest independent set inside `X` has size

```
α(G[X]) = max (a, 1)   if b = 0, or if I ∩ J = ∅
α(G[X]) = max (a, 2)   if I ∩ J ≠ ∅
```

The reason is that the clique vertex `b_j` is adjacent to every `a_i` with `i ≠ j`, so an independent
set containing `b_j` contains **at most** `a_j` from the independent side: the size-two witness is
the *edge* `{a_j, b_j}` — which is why the matching edge is absent.  The counting input of the proof
is

```
a + b = |I ∩ J| + |I ∪ J|,   |I ∩ J| ≤ min a b,   |I ∪ J| ≤ n.
```

## What is *not* proved

`jsp_000090_main` is not declared and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is unchanged: this file is about a *class*, and it makes one
statement about the general constant — the lower bound `f(k) ≥ k + 1` — not the upper bound, which
is the theorem.

## Toolchain notes

* The witness lives on `Fin n × Bool`; its two sides are `Finset.image`s of `Finset.univ`, so
  `Finset.card_image_of_injective` gives their sizes and **no `Finset.filter` is needed anywhere**.
* This file declares **no** `DecidableEq` instance of its own.  The instance `Split.lean` used to
  elaborate the intersection *inside* `SplitPartition` (`JSP90.instDecidableEqSplitGraph`) survives
  in its `.olean` and is found by instance search for *any* type, so an intersection built here and
  one built there do not match.  The only intersection this file may therefore build inside a
  *statement* is the one inside the goal `SplitPartition (splitWitness n) (swA n) (swB n)`, which
  `splitWitness_splitPartition` proves in place; every other statement is intersection-free, and the
  intersections of the `LocIndep` proof are private to it.  For the same reason
  `JSP90.exists_mem_sdiff_pair_of_card_ge_three` of `Split.lean` is **not** used here (its `∖` term
  carries the other instance): the difference set is built here directly.
* `Prod.mk.inj` does **not** exist at this revision: use `Prod.ext_iff.mp` on a product equality, or
  `Prod.ext` with the two field equalities *in the order of the goal*.
* Every application — `Prod.ext`, `Finset.mem_union.mpr`, `Finset.mem_insert.mpr`, `absurd` — is
  elaborated **backwards** from the expected type, and anonymous-constructor arguments (`⟨a, b⟩`,
  `Or.inl a`) are elaborated *before* the expected type is known.  Whenever the finsets are not
  already fixed by the goal, instance search then runs on a metavariable and picks the wrong
  `DecidableEq`.  So: give the finsets as named arguments (`Finset.card_le_card (s := _) (t := _)`),
  use `refine ⟨a, ?_⟩` instead of `⟨a, by …⟩`, and bind intermediates with `have`.
* Membership in a `Finset` is `Quot.lift`-based, so `p ∈ s ∩ t` has **no** projections: use
  `Finset.mem_inter.mp/.mpr` (also for a `Set`-coerced finset, whose membership unfolds to the same
  `Finset.Mem`).  `.1`/`.2` work only on the *result* of `Finset.mem_inter.mp`, and a
  `Finset.Subset` must be applied to a point *before* `Finset.mem_union.mp`/`Finset.mem_sdiff.mp` is
  applied to it.  `hnot.1` is also unavailable when `hnot : ¬ G.Adj p q`, since `Adj` unfolds to a
  conjunction only after `intro`.
* `Finset.not_mem_empty` does not exist; `Finset.eq_empty_iff_forall_notMem : s = ∅ ↔ ∀ x, x ∉ s`
  takes `x` **explicitly**, so it is applied as `... .mpr fun p hp => ...`, and `x ∉ s` is
  `x ∈ s → False`, so it can only *refute* membership, never produce it.
* `Finset.Nonempty` is `∃ x, x ∈ s`, so `Finset.nonempty_iff_ne_empty.mpr` is applied to a
  hypothesis `s ≠ ∅`; bind the result with a `have` (in an `obtain` the finsets stay undetermined).
* `Finset.card_image_iff : #(s.image f) = #s ↔ Set.InjOn f s` already has the orientation
  `((s.image f).card = s.card)`, so no `.symm`; and the `Set.InjOn` witness must be an anonymous
  function `fun _ ha _ hb hab => ...`, since both membership hypotheses are implicit.
* `Finset.card_union_add_card_inter : #(s ∪ t).card + #(s ∩ t).card = #s + #t` — the *union* comes
  first, so a goal `s.card + t.card = _` needs `←`, and `←` rewrites the **leftmost** occurrence,
  which is not always the one intended.  `Finset.card_union_of_disjoint` takes the `Disjoint` proof
  as its argument.
* `(0 : Fin n)` and `(1 : Fin n)` need `NeZero n` and do not elaborate for a variable `n`, so the
  two vertices of the independent side are parameters `i j : Fin n` with `i ≠ j`, and the concrete
  numerals are introduced locally through `haveI : NeZero (k + 2) := ⟨by omega⟩`.
* A `Bool` equality such as `(j, true).2 = false` is refuted by neither `simp` nor `omega` at this
  revision: use `JSP90.bool_false_ne_true` / `JSP90.not_eq_false_of_eq_true`.  `by simp` *does*
  refute `false = true`, and `by omega` refutes `↑a = ↑b` for `Fin` numerals.
* `Finset.mem_filter.mp` cannot be applied to `h : S ∈ indepSets G X` from outside `Deficiency.lean`:
  the filter predicate is not unfolded, so `p` and `inst` stay metavariables and instance search
  fails.  Use `JSP90.isIndepSet_of_mem_indepSets` (added in this round) instead.
* `Finset.mem_insert.mpr h` for `h : p ∈ insert b t` gives `p = b ∨ p ∈ t` (element first), and for
  the two-element finset `{(i, false), (j, false)} = insert (i, false) {(j, false)}` the second
  disjunct is still a *membership*, so it needs `Finset.mem_singleton.mp` before `congrArg Prod.snd`.
* `Erdős73On` must be instantiated at `.{0}`: the witness lives on `Fin (k+2) × Bool : Type 0`, so
  quantifying `W : Type u` for an arbitrary `u` makes the statement unprovable.
-/
import JSPProblem.Split

namespace JSP90

open Finset Fintype Set

noncomputable section

variable {n : ℕ}

/-! ## Part 0 — `Bool` and `Prod` lemmas, used everywhere below -/

/-- **A `Bool` cannot be `false` and `true` at once.** -/
theorem bool_false_ne_true (b : Bool) (h₁ : b = false) (h₂ : b = true) : False :=
  absurd (h₁.symm.trans h₂) (by simp)

/-- **A `Bool` that is `true` is not `false`.** -/
theorem not_eq_false_of_eq_true {b : Bool} (h : b = true) : ¬ (b = false) :=
  fun hc => bool_false_ne_true b hc h

/-- **A vertex of the independent side is of the form `(i, false)`.** -/
theorem eq_pair_snd_false (p : Fin n × Bool) (h : p.2 = false) : p = (p.1, false) :=
  Prod.ext rfl h

/-- **A vertex of the clique side is of the form `(i, true)`.** -/
theorem eq_pair_snd_true (p : Fin n × Bool) (h : p.2 = true) : p = (p.1, true) :=
  Prod.ext rfl h

/-! ## Part 1 — the witness graph and its two sides -/

/-- **THE WITNESS OF THE SPLIT-GRAPH AXIS.**  On `Fin n × Bool` the vertex `(i, false)` is the
`i`-th vertex of the **independent** side and `(i, true)` the `i`-th vertex of the **clique** side;
two vertices are adjacent when their indices differ and it is not the case that both lie on the
independent side.

So `A = {(i, false)}` is independent, `B = {(i, true)}` is a clique, and `a_i ~ b_j` exactly when
`i ≠ j`.  This is the split graph in which Erdős's hypothesis `LocIndep (n − 2)` holds while the
number of vertices one must delete to make the graph bipartite is `n − 1`. -/
def splitWitness (n : ℕ) : SimpleGraph (Fin n × Bool) where
  Adj p q := p.1 ≠ q.1 ∧ ¬ (p.2 = false ∧ q.2 = false)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hcon => h.2 ⟨hcon.2, hcon.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem splitWitness_adj {n : ℕ} {p q : Fin n × Bool} :
    (splitWitness n).Adj p q ↔ p.1 ≠ q.1 ∧ ¬ (p.2 = false ∧ q.2 = false) := Iff.rfl

/-- **The independent side** of `splitWitness n`: one vertex per index. -/
def swA (n : ℕ) : Finset (Fin n × Bool) :=
  (Finset.univ : Finset (Fin n)).image (fun i => (i, false))

/-- **The clique side** of `splitWitness n`: one vertex per index. -/
def swB (n : ℕ) : Finset (Fin n × Bool) :=
  (Finset.univ : Finset (Fin n)).image (fun i => (i, true))

@[simp] theorem mem_swA {n : ℕ} {p : Fin n × Bool} : p ∈ swA n ↔ p.2 = false := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, -, rfl⟩
    rfl
  · intro h
    refine Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
    exact (eq_pair_snd_false p h).symm

@[simp] theorem mem_swB {n : ℕ} {p : Fin n × Bool} : p ∈ swB n ↔ p.2 = true := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, -, rfl⟩
    rfl
  · intro h
    refine Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
    exact (eq_pair_snd_true p h).symm

theorem card_swA : (swA n).card = n := by
  have hinj : Function.Injective (fun i : Fin n => (i, false)) :=
    fun a b hab => (Prod.ext_iff.mp hab).1
  have h := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hinj
  simpa [swA] using h

theorem card_swB : (swB n).card = n := by
  have hinj : Function.Injective (fun i : Fin n => (i, true)) :=
    fun a b hab => (Prod.ext_iff.mp hab).1
  have h := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hinj
  simpa [swB] using h

/-- **Two vertices of the independent side are never adjacent.** -/
theorem not_adj_swA {p q : Fin n × Bool} (hp : p.2 = false) (hq : q.2 = false) :
    ¬ (splitWitness n).Adj p q := by
  intro h
  exact h.2 ⟨hp, hq⟩

/-- **The independent side is an independent set.** -/
theorem isIndepSet_swA : (splitWitness n).IsIndepSet (swA n) := by
  refine isIndepSet_of_intro fun p q hp hq hne hadj => ?_
  have hp' := mem_swA.mp (Finset.mem_coe.mpr hp)
  have hq' := mem_swA.mp (Finset.mem_coe.mpr hq)
  exact not_adj_swA hp' hq' hadj

/-- **The clique side is a clique.** -/
theorem adj_of_mem_swB {p q : Fin n × Bool} (hp : p ∈ swB n) (hq : q ∈ swB n) (hne : p ≠ q) :
    (splitWitness n).Adj p q := by
  have hp' := mem_swB.mp hp
  have hq' := mem_swB.mp hq
  refine ⟨?_, ?_⟩
  · intro hEq
    have hprod : p = q := Prod.ext hEq (hp'.trans hq'.symm)
    exact hne hprod
  · rintro ⟨hpf, hqf⟩
    exact bool_false_ne_true p.2 hpf hp'

/-- **The matching edge `a_j b_j` is missing**: the cross edges are exactly the non-matching ones. -/
theorem not_adj_swA_swB_same (j : Fin n) : ¬ (splitWitness n).Adj (j, false) (j, true) := by
  intro h
  exact (splitWitness_adj.mp h).1 rfl

/-- **THE SIZE-TWO WITNESS `{a_j, b_j}` IS INDEPENDENT.** -/
theorem isIndepSet_pair_swB (j : Fin n) :
    (splitWitness n).IsIndepSet ({(j, false), (j, true)} : Finset (Fin n × Bool)) := by
  refine isIndepSet_of_intro fun p q hp hq hne hadj => ?_
  rcases Finset.mem_insert.mp (Finset.mem_coe.mpr hp) with hp' | hp'
  · rcases Finset.mem_insert.mp (Finset.mem_coe.mpr hq) with hq' | hq'
    · obtain rfl := hp'
      obtain rfl := hq'
      exact (splitWitness n).loopless.irrefl _ hadj
    · obtain rfl := hp'
      obtain rfl := Finset.mem_singleton.mp hq'
      exact not_adj_swA_swB_same _ hadj
  · rcases Finset.mem_insert.mp (Finset.mem_coe.mpr hq) with hq' | hq'
    · obtain rfl := hq'
      obtain rfl := Finset.mem_singleton.mp hp'
      exact (not_adj_swA_swB_same _ hadj.symm).elim
    · obtain rfl := Finset.mem_singleton.mp hp'
      obtain rfl := Finset.mem_singleton.mp hq'
      exact (splitWitness n).loopless.irrefl _ hadj

/-- **The two sides of `splitWitness n` are disjoint.** -/
theorem disjoint_swA_swB : Disjoint (swA n) (swB n) := by
  refine Finset.disjoint_left.2 fun p hp hq => ?_
  have h1 : p.2 = false := mem_swA.mp hp
  have h2 : p.2 = true := mem_swB.mp hq
  exact bool_false_ne_true p.2 h1 h2

/-! ## Part 2 — `splitWitness n` is a split graph, with no isolated pair -/

/-- **`splitWitness n` carries a split partition with `n` vertices on each side.** -/
theorem splitWitness_splitPartition (n : ℕ) :
    SplitPartition (splitWitness n) (swA n) (swB n) := by
  refine ⟨?_, isIndepSet_swA, ?_, ?_⟩
  · refine Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    simp only [Finset.mem_inter] at hp
    rcases hp with ⟨h1, h2⟩
    have h1' : p.2 = false := mem_swA (n := n) (p := p).mp h1
    have h2' : p.2 = true := mem_swB (n := n) (p := p).mp h2
    exact bool_false_ne_true p.2 h1' h2'
  · intro p q hp hq hne
    exact adj_of_mem_swB hp hq hne
  · ext p
    simp only [Finset.mem_union]
    constructor
    · intro _
      exact Finset.mem_univ p
    · intro _
      by_cases h : p.2 = false
      · refine Or.inl ?_
        exact mem_swA (n := n) (p := p).mpr h
      · refine Or.inr ?_
        exact mem_swB (n := n) (p := p).mpr (by simpa using h)

/-- **Every pair of the clique side of `splitWitness n` has a common neighbour in the independent
side, as soon as `3 ≤ n`.**  This rules out an isolated pair, hence the `|B| − 2` regime of
`closeToBipartite_split_iff`, and with it the constant `k` of the conclusion. -/
theorem not_isolatedPair_splitWitness {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsolatedPair (splitWitness n) (swA n) (swB n) := by
  rintro ⟨b₁, b₂, hb₁, hb₂, hne, hnc⟩
  have hb₁' : b₁ = (b₁.1, true) := eq_pair_snd_true b₁ (mem_swB.mp hb₁)
  have hb₂' : b₂ = (b₂.1, true) := eq_pair_snd_true b₂ (mem_swB.mp hb₂)
  have hne' : b₁.1 ≠ b₂.1 := by
    intro hc
    have hprod : (b₁.1, true) = (b₂.1, true) := Prod.ext hc rfl
    exact hne (hb₁'.trans (hprod.trans hb₂'.symm))
  have hunivcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hcardsub : ((Finset.univ : Finset (Fin n)) \ ({b₁.1, b₂.1} : Finset (Fin n))).card
      = n - 2 := by
    rw [Finset.card_sdiff_of_subset (fun _ ha => Finset.mem_univ _),
      Finset.card_eq_two.mpr ⟨b₁.1, b₂.1, hne', rfl⟩, hunivcard]
  have hneS : ¬ ((Finset.univ : Finset (Fin n)) \ ({b₁.1, b₂.1} : Finset (Fin n))) = ∅ := by
    intro hcon
    have hz : ((Finset.univ : Finset (Fin n)) \ ({b₁.1, b₂.1} : Finset (Fin n))).card = 0 := by
      rw [hcon, Finset.card_empty]
    rw [hcardsub] at hz
    omega
  have hNonempty : ((Finset.univ : Finset (Fin n)) \ ({b₁.1, b₂.1} : Finset (Fin n))).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hneS
  obtain ⟨m, hm⟩ := hNonempty
  have hnb : m ∉ ({b₁.1, b₂.1} : Finset (Fin n)) := (Finset.mem_sdiff.mp hm).2
  have hmb₁ : m ≠ b₁.1 := fun hc => hnb (Finset.mem_insert.mpr (Or.inl hc))
  have hmb₂ : m ≠ b₂.1 := fun hc =>
    hnb (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hc)))
  have hAdj₁ : (splitWitness n).Adj (m, false) b₁ := by
    refine ⟨by simpa using hmb₁, ?_⟩
    intro hcon
    exact bool_false_ne_true b₁.2 hcon.2 (mem_swB.mp hb₁)
  have hAdj₂ : (splitWitness n).Adj (m, false) b₂ := by
    refine ⟨by simpa using hmb₂, ?_⟩
    intro hcon
    exact bool_false_ne_true b₂.2 hcon.2 (mem_swB.mp hb₂)
  exact hnc (m, false) (mem_swA.mpr rfl) ⟨hAdj₁, hAdj₂⟩

/-! ## Part 3 — Erdős's hypothesis holds on the witness -/

/-- **A vertex of a two-element piece of the independent side lies on the independent side.** -/
theorem snd_eq_false_of_mem_pair {i j : Fin n} {p : Fin n × Bool}
    (hp : p ∈ ({(i, false), (j, false)} : Finset (Fin n × Bool))) : p.2 = false := by
  rcases Finset.mem_insert.mp hp with h | h
  · exact congrArg Prod.snd h
  · exact congrArg Prod.snd (Finset.mem_singleton.mp h)

/-- **A two-element piece of the independent side is an independent set.** -/
theorem isIndepSet_pair_swA {i j : Fin n} :
    (splitWitness n).IsIndepSet ({(i, false), (j, false)} : Finset (Fin n × Bool)) := by
  refine isIndepSet_of_intro fun p q hp hq hne hadj => ?_
  have hp' := snd_eq_false_of_mem_pair (Finset.mem_coe.mpr hp)
  have hq' := snd_eq_false_of_mem_pair (Finset.mem_coe.mpr hq)
  exact hadj.2 ⟨hp', hq'⟩

/-- **The independent number of `B ∪ {(i, false), (j, false)}` is exactly two** (for `i ≠ j`).

This is the step that computes the deficiency `|X| − 2 α(X) = (n + 2) − 4 = n − 2` of the witness:
the clique side has independence number one, and adjoining two vertices of the independent side
raises it to exactly two. -/
theorem indepCard_two {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    indepCard (splitWitness n) (swB n ∪ {(i, false), (j, false)}) = 2 := by
  have hsub0 : ({(i, false), (j, false)} : Finset (Fin n × Bool)) ⊆
      swB n ∪ {(i, false), (j, false)} := fun _ h => Finset.mem_union.mpr (Or.inr h)
  have hne : ((i, false) : Fin n × Bool) ≠ (j, false) := fun heq => hij (congrArg Prod.fst heq)
  have hlo : 2 ≤ indepCard (splitWitness n) (swB n ∪ {(i, false), (j, false)}) := by
    have h2 := le_indepCard_of_isIndepSet hsub0 (isIndepSet_pair_swA (i := i) (j := j))
    rw [Finset.card_eq_two.mpr ⟨(i, false), (j, false), hne, rfl⟩] at h2
    exact h2
  have hhi : indepCard (splitWitness n) (swB n ∪ {(i, false), (j, false)}) ≤ 2 := by
    refine Finset.sup_le_iff.mpr fun S hS => ?_
    have hSsub : S ⊆ swB n ∪ {(i, false), (j, false)} := sub_of_mem_indepSets hS
    have hSi : (splitWitness n).IsIndepSet S := isIndepSet_of_mem_indepSets hS
    have honeB : ∀ b c : Fin n × Bool, b ∈ S → c ∈ S → b ∈ swB n → c ∈ swB n → b = c := by
      intro b c hb hc hbb hcb
      by_contra hne
      exact IsIndepSet.apply' hSi hb hc hne (adj_of_mem_swB hbb hcb hne)
    by_cases hB0 : S ∩ swB n = ∅
    · have hsub : S ⊆ ({(i, false), (j, false)} : Finset (Fin n × Bool)) := by
        intro p hp
        rcases Finset.mem_union.mp (hSsub hp) with hp' | hp'
        · exact absurd (Finset.mem_inter.mpr ⟨hp, hp'⟩)
            (Finset.eq_empty_iff_forall_notMem.mp hB0 p)
        · exact hp'
      refine le_trans (Finset.card_le_card (s := S) (t := {(i, false), (j, false)}) hsub) ?_
      rw [Finset.card_eq_two.mpr ⟨(i, false), (j, false), hne, rfl⟩]
    · have hneB : (S ∩ swB n).Nonempty := Finset.nonempty_iff_ne_empty.mpr hB0
      obtain ⟨b, hb⟩ := hneB
      have hb2 : b.2 = true := mem_swB.mp (Finset.mem_inter.mp hb).2
      have hsub : S ⊆ (insert b ({(b.1, false)} : Finset (Fin n × Bool))) := by
        intro p hp
        rcases Finset.mem_union.mp (hSsub hp) with hp' | hp'
        · have hpb : p = b := honeB p b hp (Finset.mem_inter.mp hb).1 hp'
            (Finset.mem_inter.mp hb).2
          exact Finset.mem_insert.mpr (Or.inl hpb)
        · by_cases hpb : p ∈ swB n
          · have heqb : p = b := honeB p b hp (Finset.mem_inter.mp hb).1 hpb
              (Finset.mem_inter.mp hb).2
            exact Finset.mem_insert.mpr (Or.inl heqb)
          · have hpbne : p ≠ b := fun heq => hpb (heq ▸ (Finset.mem_inter.mp hb).2)
            have hnot : ¬ (splitWitness n).Adj p b :=
              IsIndepSet.apply' hSi hp (Finset.mem_inter.mp hb).1 hpbne
            have hsecond : ¬ (p.2 = false ∧ b.2 = false) := fun hcon =>
              bool_false_ne_true b.2 hcon.2 hb2
            have h1 : p.1 = b.1 := by
              by_contra hcon
              exact hnot ⟨hcon, hsecond⟩
            have h2 : p.2 = false := snd_eq_false_of_mem_pair hp'
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h1 h2)))
      have hne2 : b ≠ (b.1, false) :=
        fun heq => bool_false_ne_true b.2 (congrArg Prod.snd heq) hb2
      refine le_trans (Finset.card_le_card (s := S)
        (t := insert b ({(b.1, false)} : Finset (Fin n × Bool))) hsub) ?_
      rw [Finset.card_eq_two.mpr ⟨b, (b.1, false), hne2, rfl⟩]
  exact le_antisymm hhi hlo

/-- **The independent side meets any vertex set in an independent set.** -/
theorem isIndepSet_inter_swA (n : ℕ) (X : Finset (Fin n × Bool)) :
    (splitWitness n).IsIndepSet ((X ∩ swA n : Finset (Fin n × Bool)) : Set (Fin n × Bool)) := by
  refine IsIndepSet.subset isIndepSet_swA ?_
  intro p hp
  exact (Finset.mem_inter.mp (Finset.mem_coe.mpr hp)).2

/-- **ERDŐS'S HYPOTHESIS HOLDS ON THE WITNESS:** `LocIndep k (splitWitness (k + 2))` for every
`k ≥ 0`.

The independent set is described in the file header; the counting input is the identity
`|X ∩ A| + |X ∩ B| = |I ∩ J| + |I ∪ J|` for the two index sets `I`, `J`, together with
`|I ∩ J| ≤ min |X ∩ A| |X ∩ B|` and `|I ∪ J| ≤ n`. -/
theorem locIndep_splitWitness_aux (n k : ℕ) (hn : n = k + 2) : LocIndep k (splitWitness n) := by
  intro X
  have hXA : ∀ p : Fin n × Bool, p ∈ X → p ∈ X ∩ swA n ∨ p ∈ X ∩ swB n := by
    intro p hp
    by_cases hb : p.2 = false
    · exact Or.inl (Finset.mem_inter.mpr ⟨hp, mem_swA.mpr hb⟩)
    · exact Or.inr (Finset.mem_inter.mpr ⟨hp, mem_swB.mpr (by simpa using hb)⟩)
  have hAC : (X ∩ swA n) ∩ (X ∩ swB n) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    have h1 : p.2 = false :=
      mem_swA (n := n) (p := p).mp (Finset.mem_inter.mp (Finset.mem_inter.mp hp).1).2
    have h2 : p.2 = true :=
      mem_swB (n := n) (p := p).mp (Finset.mem_inter.mp (Finset.mem_inter.mp hp).2).2
    exact bool_false_ne_true p.2 h1 h2
  have hXsub : X.card ≤ (X ∩ swA n ∪ X ∩ swB n).card :=
    Finset.card_le_card (s := X) (t := X ∩ swA n ∪ X ∩ swB n)
      (fun p hp => Finset.mem_union.mpr (hXA p hp))
  have hXsup : (X ∩ swA n ∪ X ∩ swB n) ⊆ X := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_inter.mp h).1
    · exact (Finset.mem_inter.mp h).1
  have hXunion : X.card = (X ∩ swA n ∪ X ∩ swB n).card :=
    le_antisymm hXsub (Finset.card_le_card hXsup)
  have hXcard : X.card = (X ∩ swA n).card + (X ∩ swB n).card := by
    refine le_antisymm (le_trans hXsub ?_) ?_
    · rw [← Finset.card_union_add_card_inter, hAC, Finset.card_empty]
      omega
    · have h2 : (X ∩ swA n ∪ X ∩ swB n).card + ((X ∩ swA n) ∩ (X ∩ swB n)).card
          = (X ∩ swA n).card + (X ∩ swB n).card :=
        Finset.card_union_add_card_inter (X ∩ swA n) (X ∩ swB n)
      rw [hAC, Finset.card_empty, Nat.add_zero] at h2
      omega
  have hCsub : (X ∩ swB n).card ≤ (swB n).card :=
    Finset.card_le_card (s := X ∩ swB n) (t := swB n)
      (fun _ hp => (Finset.mem_inter.mp hp).2)
  have hCCard : (X ∩ swB n).card ≤ n := le_trans hCsub (le_of_eq (card_swB (n := n)))
  have hIcard : ((X ∩ swA n).image Prod.fst).card = (X ∩ swA n).card := by
    refine Finset.card_image_iff.mpr ?_
    intro _ ha _ hb hab
    have k1 := mem_swA.mp (Finset.mem_inter.mp ha).2
    have k2 := mem_swA.mp (Finset.mem_inter.mp hb).2
    exact Prod.ext hab (k1.trans k2.symm)
  have hJcard : ((X ∩ swB n).image Prod.fst).card = (X ∩ swB n).card := by
    refine Finset.card_image_iff.mpr ?_
    intro _ ha _ hb hab
    have k1 := mem_swB.mp (Finset.mem_inter.mp ha).2
    have k2 := mem_swB.mp (Finset.mem_inter.mp hb).2
    exact Prod.ext hab (k1.trans k2.symm)
  have hab : ((X ∩ swA n).image Prod.fst ∪ (X ∩ swB n).image Prod.fst).card
      + ((X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst).card
      = (X ∩ swA n).card + (X ∩ swB n).card := by
    rw [Finset.card_union_add_card_inter, hIcard, hJcard]
  have hia : ((X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst).card
      ≤ (X ∩ swA n).card := by
    rw [← hIcard]
    exact Finset.card_le_card
      (s := (X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst)
      (t := (X ∩ swA n).image Prod.fst)
      (fun _ ha => (Finset.mem_inter.mp ha).1)
  have hib : ((X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst).card
      ≤ (X ∩ swB n).card := by
    rw [← hJcard]
    exact Finset.card_le_card
      (s := (X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst)
      (t := (X ∩ swB n).image Prod.fst)
      (fun _ ha => (Finset.mem_inter.mp ha).2)
  have hUle : ((X ∩ swA n).image Prod.fst ∪ (X ∩ swB n).image Prod.fst).card ≤ n := by
    refine le_trans (Finset.card_le_card
      (s := (X ∩ swA n).image Prod.fst ∪ (X ∩ swB n).image Prod.fst)
      (t := (Finset.univ : Finset (Fin n))) (fun _ _ => Finset.mem_univ _)) ?_
    exact le_of_eq (by simp)
  by_cases hC0 : (X ∩ swB n) = ∅
  · refine ⟨X ∩ swA n, Finset.inter_subset_left, isIndepSet_inter_swA n X, ?_⟩
    rw [hXcard, hC0, Finset.card_empty, Nat.add_zero]
    omega
  · have hneC : (X ∩ swB n).Nonempty := Finset.nonempty_iff_ne_empty.mpr hC0
    by_cases hA0 : (X ∩ swA n) = ∅
    · obtain ⟨c, hc⟩ := hneC
      refine ⟨{c}, Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hc).1,
        isIndepSet_singleton _ _, ?_⟩
      rw [hXcard, hA0, Finset.card_empty, Nat.zero_add]
      have hone : 2 * ({c} : Finset (Fin n × Bool)).card = 2 := by simp
      rw [hone]
      exact le_trans hCCard (by omega)
    · have hneA : (X ∩ swA n).Nonempty := Finset.nonempty_iff_ne_empty.mpr hA0
      by_cases hA1 : (X ∩ swA n).card = 1
      · obtain ⟨a₀, ha₀⟩ := hneA
        by_cases hinter : ((X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst) = ∅
        · have hz : ((X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst).card = 0 :=
            Finset.card_eq_zero.mpr hinter
          refine ⟨{a₀}, Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp ha₀).1,
            isIndepSet_singleton _ _, ?_⟩
          rw [hXcard, hA1]
          have hone : 2 * ({a₀} : Finset (Fin n × Bool)).card = 2 := by simp
          rw [hone]
          omega
        · have hneIJ :
              ((X ∩ swA n).image Prod.fst ∩ (X ∩ swB n).image Prod.fst).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hinter
          obtain ⟨j, hj⟩ := hneIJ
          obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hj).1
          have hxA : x = (j, false) := Prod.ext hxeq (mem_swA.mp (Finset.mem_inter.mp hx).2)
          obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hj).2
          have hyB : y = (j, true) := Prod.ext hyeq (mem_swB.mp (Finset.mem_inter.mp hy).2)
          have hxaX : (j, false) ∈ X := hxA ▸ (Finset.mem_inter.mp hx).1
          have hybX : (j, true) ∈ X := hyB ▸ (Finset.mem_inter.mp hy).1
          refine ⟨{(j, false), (j, true)}, ?_, isIndepSet_pair_swB j, ?_⟩
          · intro p hp
            rcases Finset.mem_insert.mp hp with hp' | hp'
            · obtain rfl := hp'
              exact hxaX
            · obtain rfl := Finset.mem_singleton.mp hp'
              exact hybX
          · have hneJT : ((j, false) : Fin n × Bool) ≠ (j, true) :=
              fun heq => bool_false_ne_true Bool.false rfl (congrArg Prod.snd heq)
            have hcard : ({(j, false), (j, true)} : Finset (Fin n × Bool)).card = 2 :=
              Finset.card_eq_two.mpr ⟨(j, false), (j, true), hneJT, rfl⟩
            rw [hcard, hXcard, hA1]
            omega
      · refine ⟨X ∩ swA n, Finset.inter_subset_left, isIndepSet_inter_swA n X, ?_⟩
        have hposA : 0 < (X ∩ swA n).card := Finset.card_pos.mpr hneA
        by_cases hba : (X ∩ swB n).card ≤ (X ∩ swA n).card
        · rw [hXcard]
          omega
        · have hle : (X ∩ swB n).card ≤ n := by omega
          rw [hXcard]
          omega

/-- **ERDŐS'S HYPOTHESIS HOLDS ON THE WITNESS, FOR EVERY `k`.** -/
theorem locIndep_splitWitness (k : ℕ) : LocIndep k (splitWitness (k + 2)) :=
  locIndep_splitWitness_aux (k + 2) k rfl

/-- **THE EXACT VALUE OF ERDŐS'S HYPOTHESIS ON THE WITNESS:** `MaxDef (splitWitness (k + 2)) = k`.

So `LocIndep k (splitWitness (k + 2))` holds and `LocIndep (k − 1)` fails, for `k ≥ 1`: the witness
is *tight* for the hypothesis, exactly as `kTriangles k` is for `LocIndep k`. -/
theorem maxDef_splitWitness {k : ℕ} (hk : 1 ≤ k) : MaxDef (splitWitness (k + 2)) = k := by
  have hk2 : 0 < k + 2 := by omega
  have hk2' : 1 < k + 2 := by omega
  set i0 : Fin (k + 2) := ⟨0, hk2⟩ with hi0
  set i1 : Fin (k + 2) := ⟨1, hk2'⟩ with hi1
  set W : Finset (Fin (k + 2) × Bool) := swB (k + 2) ∪ {(i0, false), (i1, false)} with hW
  have hne01 : ((i0, false) : Fin (k + 2) × Bool) ≠ (i1, false) := by
    intro heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Fin.val h1
    have h3 : (0 : ℕ) = 1 := by simpa only [hi1, hi0, Fin.val_mk] using h2
    exact absurd h3.symm (Nat.succ_ne_zero 0)
  have hdisj : Disjoint (swB (k + 2))
      ({(i0, false), (i1, false)} : Finset (Fin (k + 2) × Bool)) := by
    refine Finset.disjoint_left.2 fun p hp hq => ?_
    have h1 := mem_swB.mp hp
    rcases Finset.mem_insert.mp hq with h | h
    · exact bool_false_ne_true p.2 (congrArg Prod.snd h) h1
    · exact bool_false_ne_true p.2 (congrArg Prod.snd (Finset.mem_singleton.mp h)) h1
  have hcard : W.card = k + 4 := by
    rw [hW, Finset.card_union_of_disjoint hdisj, card_swB,
      Finset.card_eq_two.mpr ⟨(i0, false), (i1, false), hne01, rfl⟩, Nat.add_assoc]
  have h2 : indepCard (splitWitness (k + 2)) W = 2 := by
    rw [hW]
    exact indepCard_two (n := k + 2) (i := i0) (j := i1)
      (fun heq => hne01 (Prod.ext heq rfl))
  have hlo : k ≤ MaxDef (splitWitness (k + 2)) := by
    have h1 := le_maxDef (splitWitness (k + 2)) W
    have h3 : 2 * indepCard (splitWitness (k + 2)) W = 4 := by
      rw [h2]
    rw [defOf, h3, hcard, Nat.add_sub_cancel] at h1
    exact h1
  exact le_antisymm (maxDef_le_of_locIndep (locIndep_splitWitness k)) hlo

/-! ## Part 4 — the conclusion, and the lower bound on the constant of Erdős #73 -/

/-- **`k + 1` VERTICES SUFFICE ON THE WITNESS.** -/
theorem closeToBipartite_splitWitness {k : ℕ} (hk : 1 ≤ k) :
    CloseToBipartite (k + 1) (splitWitness (k + 2)) := by
  have hcardpos : 0 < (swB (k + 2)).card := by rw [card_swB]; omega
  have hneB : (swB (k + 2)).Nonempty := Finset.card_pos.mp hcardpos
  exact closeToBipartite_of_splitPartition (V := Fin (k + 2) × Bool)
    (G := splitWitness (k + 2)) (k := k) (locIndep_splitWitness k)
    (splitWitness_splitPartition _) hneB

/-- **`k` VERTICES DO NOT SUFFICE ON THE WITNESS**, for `k ≥ 1`: every pair of the clique side has a
common neighbour in the independent side, so there is no isolated pair and the `|B| − 2` regime of
`closeToBipartite_split_iff` is unavailable. -/
theorem not_closeToBipartite_splitWitness {k : ℕ} (hk : 1 ≤ k) :
    ¬ CloseToBipartite k (splitWitness (k + 2)) := by
  have h2 : 2 ≤ (swB (k + 2)).card := by rw [card_swB]; omega
  have hnot : ¬ CloseToBipartite ((swB (k + 2)).card - 2) (splitWitness (k + 2)) :=
    not_closeToBipartite_of_split_no_isolatedPair (splitWitness_splitPartition _) h2
      (not_isolatedPair_splitWitness (by omega))
  intro hm
  exact hnot (closeToBipartite_mono (by rw [card_swB]; omega) hm)

/-- **THE EXACT VALUE OF THE CONCLUSION OF ERDŐS #73 ON THE WITNESS:**
`CloseToBipartite m (splitWitness (k + 2)) ↔ k + 1 ≤ m` for `k ≥ 1`.

Together with `locIndep_splitWitness` this says: on this family the hypothesis allows `k` and the
conclusion needs exactly `k + 1`. -/
theorem closeToBipartite_iff_splitWitness {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    CloseToBipartite m (splitWitness (k + 2)) ↔ k + 1 ≤ m := by
  constructor
  · intro hm
    by_contra hcon
    exact not_closeToBipartite_splitWitness hk (closeToBipartite_mono (by omega) hm)
  · intro hm
    exact closeToBipartite_mono (by omega) (closeToBipartite_splitWitness hk)

/-- **THE CONSTANT OF ERDŐS #73 IS NOT `k`: `f(k) ≥ k + 1` FOR EVERY `k ≥ 1`.**

`Erdős73On k k` is the assertion "every finite graph satisfying Erdős's hypothesis `LocIndep k` is
the union of a bipartite graph and at most `k` vertices".  This theorem refutes it, with the single
witness `splitWitness (k + 2)`.  Together with `maxDef_splitWitness` the two statements say that the
witness is tight for the hypothesis (`LocIndep k` holds, `LocIndep (k − 1)` fails) while the
conclusion on it costs exactly one vertex more than `k`.

This is the first machine-checked lower bound on the constant of JSP-000090 that is strictly larger
than the `f(k) ≥ k` of rounds 39 and 104. -/
theorem not_erdos73On_splitWitness {k : ℕ} (hk : 1 ≤ k) : ¬ Erdős73On.{0} k k := by
  intro h
  exact not_closeToBipartite_splitWitness hk
    (h (Fin (k + 2) × Bool) inferInstance (splitWitness (k + 2)) (locIndep_splitWitness k))

/-- **THERE IS NO CONSTANT BELOW `k + 1` FOR THE SPLIT-GRAPH INSTANCE OF ROUND 107.**  The statement
of `erdos73On_of_splitPartition` holds with `k + 1` and fails with `k`, so the constant of that
instance is optimal. -/
theorem erdos73On_of_splitPartition_optimal {k : ℕ} (hk : 1 ≤ k) :
    (∀ (W : Type 0) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ A B : Finset W, SplitPartition G A B → B.Nonempty → CloseToBipartite (k + 1) G)
      ∧ ¬ (∀ (W : Type 0) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
        ∀ A B : Finset W, SplitPartition G A B → B.Nonempty → CloseToBipartite k G) := by
  refine ⟨fun W _ G hG A B h hB => erdos73On_of_splitPartition hG h hB, ?_⟩
  intro h2
  have hcardpos : 0 < (swB (k + 2)).card := by rw [card_swB]; omega
  have hneB : (swB (k + 2)).Nonempty := Finset.card_pos.mp hcardpos
  exact not_closeToBipartite_splitWitness hk (h2 (Fin (k + 2) × Bool) inferInstance
    (splitWitness (k + 2)) (locIndep_splitWitness k) (swA (k + 2)) (swB (k + 2))
    (splitWitness_splitPartition _) hneB)

end
end JSP90
