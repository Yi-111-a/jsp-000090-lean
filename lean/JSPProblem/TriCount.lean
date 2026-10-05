import JSPProblem.ThreeOrder

/-!
# JSP-000090, round 165 — `JSPProblem/TriCount.lean`: **THE COUNTING STEP OF THE TRIANGLE CASE,
## AND THE CORRECTION OF ROUND 164's READING OF "BAD"**

Attack families 86 and 87.  This file executes the concrete next bet of round 164 (`policy.json`):
the `|X| = 4` sub-case of the **triangle case**, the only open case of the sharp seven-vertex axis
(`JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase`, round 162).

## The correction (this is the round's main finding)

Round 164 defined the badness of a vertex `t` of `T` through `JSP90.properX`, a `Bool` that checks
only that the **class-`{0,1}` endpoint** of a cross edge is not coloured `true`:

```lean
JSP90.properX A c = !((c 0 && (cross A 0 2 || cross A 0 3)) || (c 1 && (cross A 1 2 || cross A 1 3)))
```

That condition is **strictly weaker** than "`c` is a proper two-colouring of `G[X]`": the colouring
`c 0 = c 1 = c 2 = c 3 = false` satisfies `properX` although it is not proper at all.  So round
164's `bad8` was **not** "`G[X + {t}]` is not bipartite" but a strictly weaker condition, and the
transfer of the hypothesis "`t` is bad" into the `Fin 7` language — which needs a *proper*
two-colouring of `G[X]` — had no available tool.

The correct reading is `JSP90.proper8`, which checks **all four** cross pairs and is therefore
*equivalent* to properness (`JSP90.proper8_adj`).  With it:

* `JSP90.bad8` **is** "`G[X + {t}]` is not bipartite", and both transfer directions are available:
  `JSP90.monoS_of_all` builds the monochromatic colouring from a genuine two-colouring, and
  `JSP90.proper8_adj` reads a properness check back;
* the counting step `JSP90.loc7_lemma` keeps round 164's shape and is **proved by `decide`**:
  the three bad vertices of a triangle over a bipartite four-element residue, with the three
  neighbour sets meeting both colour classes and with empty triple intersection, leave some vertex
  of the seven **avoided by no independent triple** — while Erdős's hypothesis, read on the
  six-element subset `V \ {z}`, supplies exactly such a triple.  The triangle case follows.

The measurement behind both statements is `discovery/JSP-000090/r165c.c` (log `r165c.log`): over
all `2^4 · 2^12 = 65 536` configurations `A × S` of the `Fin 7` language, `816` have all three
vertices of `T` bad (in the corrected reading) and **none** of them has an independent triple
avoiding every one of the seven vertices (`0` violations of the conclusion above).  The same run
**refutes** the alternative conclusion that two deletions always suffice (`528` violations), which
is why the counting step is stated with the transversal conclusion.

## The mathematics

Write `X = V \ T`, `S_t = N(t) ∩ X`, and suppose all three vertices of `T` are **bad**, i.e.
`G[X + {t}]` is not bipartite for each of them.  Let `d` be a proper two-colouring of `G[X]`
(which exists by hypothesis), with classes `P` and `Q`.

1. **Each `S_t` meets both classes** (`JSP90.exists_adjIn_color`): if all residual neighbours of `t`
   carry one colour, then `G[X + {t}]` is bipartite — give `t` the other colour.
2. **Both classes have two points** (`JSP90.card_cls_ge_two`): a class with no point makes a vertex
   good, and a class with a single point `p` is met by all three vertices of `T`, so `p` is adjacent
   to all of `T`, which Erdős's hypothesis excludes.
3. Hence `|X| = 4`, `|P| = |Q| = 2`, so `G[X]` is a subgraph of `K_{2,2}` with **four cells**.
4. **A vertex of `X` is never adjacent to all of `T`**: the three sets `S_a, S_b, S_c` have empty
   triple intersection.
5. The remaining content is a **finite case analysis on the four cells of `K_{2,2}`** with the three
   neighbour sets meeting both classes: `JSP90.loc7_lemma`, closed by `decide`.

## What this file proves

* `JSP90.loc7_lemma` — the counting step above, **by `decide`** (`decide`, not `native_decide`, so
  the proof is verified by the Lean kernel and the axiom list is unchanged).
* `JSP90.proper8`, `JSP90.proper8_adj`, `JSP90.monoS_of_all`, `JSP90.bad8` — the **correct** reading
  of the local structure: `proper8 A m = true` **is** "`m` is a proper two-colouring of `G[X]`",
  and `bad8 A S t` **is** "`G[X + {t}]` is not bipartite".
* `JSP90.col4`, `JSP90.col7` — the two-colourings, packed into `Fin 16` and `Fin 128` (this is what
  keeps `loc7_lemma` within reach of `decide`).
* `JSP90.hyps_of`, `JSP90.erdos6_of_forall`, `JSP90.exists_triple_of_hasTripleAvoiding`,
  `JSP90.hasTripleAvoiding_of_indep3`, `JSP90.ofDecideTrue` — the glue between the `Fin 7` language
  and the hypotheses of `loc7_lemma`, in both directions.
* `JSP90.isBipartite_of_adjIn_mono`, `JSP90.exists_adjIn_color`, `JSP90.card_cls_ge_two` — steps 1
  and 2 above, in general form.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

local instance tcDec : DecidableEq V := Classical.decEq V

local instance tcAdj : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _


/-! ## Part 0 — the local structure, in the `Fin 7` language

`X = V \ T` is carried by `Fin 4` (the points `0,1` in one colour class of `G[X]` and `2,3` in the
other) and `T` by `Fin 3` (the points `4,5,6`).  The whole local structure is then

* `A : Fin 4 → Bool`, the four cells of `G[X]` between the two colour classes,
* `S : Fin 3 → Fin 4 → Bool`, the neighbours of `t` inside `X`. -/

/-- The index of `i` in `X = {0,1,2,3}`, if it lies in `X`. -/
def xIdx (i : Fin 7) : Option (Fin 4) := if h : i.val < 4 then some ⟨i.val, h⟩ else none

/-- The index of `i` in `T = {4,5,6}`, if it lies in `T`. -/
def tIdx (i : Fin 7) : Option (Fin 3) := if h : 4 ≤ i.val then some ⟨i.val - 4, by omega⟩ else none

/-- The four cells of `G[X]` between the two colour classes; `false` inside a class. -/
def cross (A : Fin 4 → Bool) (p q : Fin 4) : Bool :=
  if hp : p.val < 2 then (if hq : q.val < 2 then false else A ⟨2 * p.val + (q.val - 2), by omega⟩)
  else (if hq : q.val < 2 then A ⟨2 * q.val + (p.val - 2), by omega⟩ else false)

/-- The adjacency of the local structure: `X = {0,1,2,3}` bipartite with colour classes `{0,1}`
and `{2,3}`, `T = {4,5,6}` a clique, and `t` joined to the points of `S t` inside `X`. -/
def adj7 (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (i j : Fin 7) : Bool :=
  match xIdx i, tIdx i, xIdx j, tIdx j with
  | some p, none, some q, none => cross A p q
  | some p, none, none, some u => S u p
  | none, some u, some q, none => S u q
  | none, some u, none, some v => decide (u ≠ v)
  | _, _, _, _ => false

/-- **INDEPENDENCE OF THREE VERTICES** in the local structure. -/
def indep3 (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (a b c : Fin 7) : Bool :=
  (decide (a = b) || ! (adj7 A S a b)) && (decide (b = c) || ! (adj7 A S b c))
    && (decide (a = c) || ! (adj7 A S a c))

/-- **THE `m`-TH OF THE `2 ^ 7` TWO-COLOURINGS OF THE SEVEN VERTICES.**  The colour of `i` in the
colouring `m` is `m.testBit i`.  Packing the colourings into `Fin 128` (rather than ranging over
`Fin 7 → Bool`) is what keeps `JSP90.loc7_lemma` inside the reach of `decide`. -/
def col7 (m : Fin 128) (i : Fin 7) : Bool := m.val.testBit i.val

/-- **THE `m`-TH OF THE `2 ^ 4` TWO-COLOURINGS OF THE RESIDUE.** -/
def col4 (m : Fin 16) (i : Fin 4) : Bool := m.val.testBit i.val

/-- **A PROOF OF A `PROP` GIVES `decide p = true`.**  (The Lean core of this version only provides
`of_decide_eq_true : decide p = true → p`, the other direction; this is its converse, and it is
what every transfer lemma of this file uses to feed a `decide`-valued definition.) -/
theorem ofDecideTrue {p : Prop} [Decidable p] (h : p) : decide p = true :=
  decide_eq_true_iff.mpr h

/-- **A FOUR-FOLD DISJUNCTION OF BOOLS.** -/
theorem bool_four_or {a b c d : Bool} (h : (a || b || c || d) = true) :
    ((a = true ∨ b = true) ∨ c = true) ∨ d = true := by
  simp only [Bool.or_eq_true_iff] at h
  exact h

/-- **A PROPER TWO-COLOURING OF THE RESIDUE `G[X]`**, in the `Fin 7` language: adjacent residue
points get different colours.

Only the four *cross* pairs can be edges of `G[X]`, because `cross A p q = false` inside a colour
class (`cross` returns `false` when both indices are `< 2` or both are `≥ 2`), so this `Bool` is
**equivalent** to "`m` is a proper two-colouring of `G[X]`" — which is what `JSP90.proper8_adj`
records, and which the version of round 164 (`JSP90.properX`, checking only the class-`{0,1}`
endpoints) failed to be. -/
def proper8 (A : Fin 4 → Bool) (m : Fin 16) : Bool :=
  (! cross A 0 2 || decide (col4 m 0 ≠ col4 m 2))
    && (! cross A 0 3 || decide (col4 m 0 ≠ col4 m 3))
    && (! cross A 1 2 || decide (col4 m 1 ≠ col4 m 2))
    && (! cross A 1 3 || decide (col4 m 1 ≠ col4 m 3))

/-- **`proper8` IS PROPERNESS.**  Adjacent residue points get different colours. -/
theorem proper8_adj : ∀ (A : Fin 4 → Bool) (m : Fin 16) (p q : Fin 4),
    proper8 A m = true → cross A p q = true → col4 m p ≠ col4 m q := by
  decide

/-- `S t` is **monochromatic** under the colouring `m` of `X`, i.e. any two points of `S t` carry
the same colour.  Written as six guarded pairs, which is the cheap form for `decide`. -/
def monoS (S : Fin 3 → Fin 4 → Bool) (t : Fin 3) (m : Fin 16) : Bool :=
  (! S t 0 || ! S t 1 || decide (col4 m 0 = col4 m 1))
    && (! S t 0 || ! S t 2 || decide (col4 m 0 = col4 m 2))
    && (! S t 0 || ! S t 3 || decide (col4 m 0 = col4 m 3))
    && (! S t 1 || ! S t 2 || decide (col4 m 1 = col4 m 2))
    && (! S t 1 || ! S t 3 || decide (col4 m 1 = col4 m 3))
    && (! S t 2 || ! S t 3 || decide (col4 m 2 = col4 m 3))

/-- **MONOCHROMICITY, READ FORWARD.**  Any two points of `S t` carry the same colour, so `S t` is
monochromatic: this is the direction the transfer lemma `JSP90.bad8_of_not_isBipartite` needs. -/
theorem monoS_of_all {S : Fin 3 → Fin 4 → Bool} {t : Fin 3} {m : Fin 16}
    (h : ∀ x y : Fin 4, S t x = true → S t y = true → col4 m x = col4 m y) :
    monoS S t m = true := by
  have one : ∀ x y : Fin 4,
      (! S t x || ! S t y || decide (col4 m x = col4 m y)) = true := by
    intro x y
    by_cases hx : S t x = true
    · by_cases hy : S t y = true
      · have hxy : col4 m x = col4 m y := h x y hx hy
        simp [hx, hy, hxy]
      · simp [hx, hy]
    · simp [hx]
  have p01 := one 0 1
  have p02 := one 0 2
  have p03 := one 0 3
  have p12 := one 1 2
  have p13 := one 1 3
  have p23 := one 2 3
  simp only [monoS, Bool.and_eq_true_iff]
  exact ⟨⟨⟨⟨⟨p01, p02⟩, p03⟩, p12⟩, p13⟩, p23⟩

/-- **THE VERTEX `t` OF `T` IS BAD**: `G[X + {t}]` is not bipartite, i.e. **no** proper two-colouring
of `G[X]` makes `S t` monochromatic.  (Round 164 read this with the weaker `properX`.) -/
abbrev bad8 (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (t : Fin 3) : Prop :=
  ∀ m : Fin 16, ¬ (monoS S t m = true ∧ proper8 A m = true)

/-- **AN INDEPENDENT TRIPLE AVOIDING `z`**, at three *distinct* points. -/
def triple3 (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (z a b c : Fin 7) : Bool :=
  indep3 A S a b c && (decide (a ≠ z) && (decide (b ≠ z) && decide (c ≠ z)))

/-- **THERE IS AN INDEPENDENT TRIPLE AVOIDING `z`.** -/
def hasTripleAvoiding (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (z : Fin 7) : Bool :=
  (List.finRange 7).any fun a => (List.finRange 7).any fun b =>
    (decide (a ≠ b) &&
      ((List.finRange 7).any fun c => (decide (c ≠ a) && (decide (c ≠ b) && triple3 A S z a b c))))

/-- **ERDŐS'S HYPOTHESIS READ ON THE SIX-ELEMENT SUBSETS**: every vertex of the seven is avoided by
some independent triple, i.e. deleting any one vertex leaves an independent set of three. -/
def erdos6 (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) : Bool :=
  (List.finRange 7).all fun z => hasTripleAvoiding A S z

/-- The hypotheses of the counting step: each `S t` meets both colour classes, the three sets
have empty triple intersection, and each `t` is bad. -/
def hyps (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) : Bool :=
  (List.finRange 3).all (fun t => ((S t 0 || S t 1) && (S t 2 || S t 3)))
    && (List.finRange 4).all (fun i => decide ((S 0 i && S 1 i && S 2 i) = false))
    && (List.finRange 3).all (fun t => decide (bad8 A S t))

/-- **AN INDEPENDENT TRIPLE AVOIDING `z` GIVES THREE POINTS.** -/
theorem exists_triple_of_hasTripleAvoiding {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool}
    {z : Fin 7} (h : hasTripleAvoiding A S z = true) :
    ∃ a b c : Fin 7, indep3 A S a b c = true ∧ a ≠ z ∧ b ≠ z ∧ c ≠ z := by
  unfold hasTripleAvoiding at h
  obtain ⟨a, -, ha⟩ := List.any_eq_true.mp h
  obtain ⟨b, -, hb⟩ := List.any_eq_true.mp ha
  simp only [Bool.and_eq_true_iff] at hb
  obtain ⟨hab, hcrest⟩ := hb
  obtain ⟨c, -, hc⟩ := List.any_eq_true.mp hcrest
  simp only [Bool.and_eq_true_iff] at hc
  obtain ⟨hca, hrest⟩ := hc
  obtain ⟨hcb, h3⟩ := hrest
  unfold triple3 at h3
  simp only [Bool.and_eq_true_iff] at h3
  obtain ⟨hind, hrest2⟩ := h3
  obtain ⟨hz1, hrest3⟩ := hrest2
  obtain ⟨hz2, hz3⟩ := hrest3
  exact ⟨a, b, c, hind, of_decide_eq_true hz1, of_decide_eq_true hz2, of_decide_eq_true hz3⟩

/-- **AN INDEPENDENT TRIPLE AVOIDING `z` IS A WITNESS FOR `hasTripleAvoiding`.**  This is the
direction the transfer from a graph needs: three *distinct* points carrying an independent triple
and all different from `z` make `hasTripleAvoiding A S z = true`. -/
theorem hasTripleAvoiding_of_indep3 {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool}
    {z a b c : Fin 7} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hind : indep3 A S a b c = true) (ha : a ≠ z) (hb : b ≠ z) (hc : c ≠ z) :
    hasTripleAvoiding A S z = true := by
  have eab : (decide (a ≠ b)) = true := ofDecideTrue hab
  have eca : (decide (c ≠ a)) = true := ofDecideTrue (Ne.symm hac)
  have ecb : (decide (c ≠ b)) = true := ofDecideTrue (Ne.symm hbc)
  have eaz : (decide (a ≠ z)) = true := ofDecideTrue ha
  have ebz : (decide (b ≠ z)) = true := ofDecideTrue hb
  have ecz : (decide (c ≠ z)) = true := ofDecideTrue hc
  have h3 : triple3 A S z a b c = true :=
    Bool.and_eq_true_iff.mpr ⟨hind, Bool.and_eq_true_iff.mpr ⟨eaz, Bool.and_eq_true_iff.mpr ⟨ebz, ecz⟩⟩⟩
  unfold hasTripleAvoiding
  have key2 : ((List.finRange 7).any fun c => (decide (c ≠ a) && (decide (c ≠ b) && triple3 A S z a b c))) = true :=
    List.any_eq_true.mpr ⟨c, List.mem_finRange c, Bool.and_eq_true_iff.mpr ⟨eca, Bool.and_eq_true_iff.mpr ⟨ecb, h3⟩⟩⟩
  have key1 : (decide (a ≠ b) && ((List.finRange 7).any fun c =>
      (decide (c ≠ a) && (decide (c ≠ b) && triple3 A S z a b c)))) = true :=
    Bool.and_eq_true_iff.mpr ⟨eab, key2⟩
  have key0 : ((List.finRange 7).any fun b => (decide (a ≠ b) && ((List.finRange 7).any fun c =>
      (decide (c ≠ a) && (decide (c ≠ b) && triple3 A S z a b c))))) = true :=
    List.any_eq_true.mpr ⟨b, List.mem_finRange b, key1⟩
  exact List.any_eq_true.mpr ⟨a, List.mem_finRange a, key0⟩

/-- The `n`-th of the `2 ^ 4` configurations of the four cells of `G[X]`: the `i`-th cell is
`true` iff the `i`-th bit of `n` is set. -/
def aBits (n : Fin 16) : Fin 4 → Bool := fun i => decide (n.val.testBit i.val = true)

/-- **EVERY CONFIGURATION OF THE FOUR CELLS IS SOME `aBits`.** -/
theorem exists_aBits (A : Fin 4 → Bool) : ∃ n : Fin 16, aBits n = A := by
    have h0 : A 0 = true ∨ A 0 = false := Bool.eq_false_or_eq_true _
    have h1 : A 1 = true ∨ A 1 = false := Bool.eq_false_or_eq_true _
    have h2 : A 2 = true ∨ A 2 = false := Bool.eq_false_or_eq_true _
    have h3 : A 3 = true ∨ A 3 = false := Bool.eq_false_or_eq_true _
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3
    · refine ⟨⟨15, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨7, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨11, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨3, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨13, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨5, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨9, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨1, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨14, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨6, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨10, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨2, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨12, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨4, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨8, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide
    · refine ⟨⟨0, by decide⟩, ?_⟩
      funext i
      have hk' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl <;> (try simp only [h0, h1, h2, h3]) <;> decide

theorem loc7_lemma_0 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 0) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 0) S z = true)) := by
  decide

theorem loc7_lemma_1 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 1) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 1) S z = true)) := by
  decide

theorem loc7_lemma_2 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 2) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 2) S z = true)) := by
  decide

theorem loc7_lemma_3 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 3) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 3) S z = true)) := by
  decide

theorem loc7_lemma_4 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 4) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 4) S z = true)) := by
  decide

theorem loc7_lemma_5 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 5) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 5) S z = true)) := by
  decide

theorem loc7_lemma_6 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 6) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 6) S z = true)) := by
  decide

theorem loc7_lemma_7 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 7) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 7) S z = true)) := by
  decide

theorem loc7_lemma_8 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 8) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 8) S z = true)) := by
  decide

theorem loc7_lemma_9 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 9) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 9) S z = true)) := by
  decide

theorem loc7_lemma_10 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 10) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 10) S z = true)) := by
  decide

theorem loc7_lemma_11 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 11) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 11) S z = true)) := by
  decide

theorem loc7_lemma_12 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 12) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 12) S z = true)) := by
  decide

theorem loc7_lemma_13 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 13) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 13) S z = true)) := by
  decide

theorem loc7_lemma_14 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 14) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 14) S z = true)) := by
  decide

theorem loc7_lemma_15 : ∀ (S : Fin 3 → Fin 4 → Bool), hyps (aBits 15) S = true →
    ¬ ((∀ z : Fin 7, hasTripleAvoiding (aBits 15) S z = true)) := by
  decide

/-- **THE COUNTING STEP, IN THE CORRECTED READING.**  Three bad vertices of a triangle over a
bipartite four-element residue, the three neighbour sets meeting both colour classes, and the three
sets with empty triple intersection: then **some vertex of the seven is avoided by no independent
triple**, which contradicts Erdős's hypothesis read on the six-element subset `V \ {z}`.

The statement is closed by `decide` — sixteen times, once for each of the `2 ^ 4` configurations of
the four cells of `G[X]` (`JSP90.loc7_lemma_0 … JSP90.loc7_lemma_15`), which is what keeps the
kernel elaboration inside its memory budget (a single `decide` over the `2 ^ 16` configurations is
killed by the kernel after ~370 s).  So the Lean kernel itself verifies the finite case analysis
(`discovery/JSP-000090/r165c.c`: `816` configurations satisfy the three hypotheses, `0` violate this
conclusion). -/
theorem loc7_lemma : ∀ (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool),
    hyps A S = true → ¬ ((∀ z : Fin 7, hasTripleAvoiding A S z = true)) := by
  intro A S hA hE
  obtain ⟨n, hn⟩ := exists_aBits A
  rw [← hn] at hA hE
  fin_cases n
  · exact loc7_lemma_0 S hA hE
  · exact loc7_lemma_1 S hA hE
  · exact loc7_lemma_2 S hA hE
  · exact loc7_lemma_3 S hA hE
  · exact loc7_lemma_4 S hA hE
  · exact loc7_lemma_5 S hA hE
  · exact loc7_lemma_6 S hA hE
  · exact loc7_lemma_7 S hA hE
  · exact loc7_lemma_8 S hA hE
  · exact loc7_lemma_9 S hA hE
  · exact loc7_lemma_10 S hA hE
  · exact loc7_lemma_11 S hA hE
  · exact loc7_lemma_12 S hA hE
  · exact loc7_lemma_13 S hA hE
  · exact loc7_lemma_14 S hA hE
  · exact loc7_lemma_15 S hA hE
/-- **ERDŐS'S CONDITION, PACKED.**  `erdos6 A S = true` iff every vertex of the seven has an
independent triple avoiding it. -/
theorem erdos6_of_forall {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool}
    (h : ∀ z : Fin 7, hasTripleAvoiding A S z = true) : erdos6 A S = true := by
  apply List.all_eq_true.mpr
  intro z _
  exact h z

/-- The hypotheses of `loc7_lemma` are exactly the three conditions of the counting step. -/
theorem hyps_of {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool}
    (h2 : ∀ t : Fin 3, S t 0 = true ∨ S t 1 = true)
    (h3 : ∀ t : Fin 3, S t 2 = true ∨ S t 3 = true)
    (h1 : ∀ i : Fin 4, S 0 i = true → S 1 i = true → S 2 i = true → False)
    (h4 : ∀ t : Fin 3, bad8 A S t) :
    hyps A S = true := by
  have h2' : (List.finRange 3).all (fun t => ((S t 0 || S t 1) && (S t 2 || S t 3))) = true := by
    apply List.all_eq_true.mpr
    intro t _
    simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff]
    exact ⟨h2 t, h3 t⟩
  have h1' : (List.finRange 4).all (fun i => decide ((S 0 i && S 1 i && S 2 i) = false)) = true := by
    apply List.all_eq_true.mpr
    intro i _
    refine decide_eq_true (Bool.eq_false_of_not_eq_true ?_)
    intro hpos
    simp only [Bool.and_eq_true_iff] at hpos
    exact h1 i hpos.1.1 hpos.1.2 hpos.2
  have h4' : (List.finRange 3).all (fun t => decide (bad8 A S t)) = true := by
    apply List.all_eq_true.mpr
    intro t _
    exact decide_eq_true (h4 t)
  refine Bool.and_eq_true_iff.mpr ⟨?_, h4'⟩
  exact Bool.and_eq_true_iff.mpr ⟨h2', h1'⟩

/-! ## Part 1 — TWO COLOURING LEMMAS -/

/-- The other of the two colours of `Fin 2`. -/
def opp2 (i : Fin 2) : Fin 2 := ⟨(i.val + 1) % 2, Nat.mod_lt _ (by decide)⟩

@[simp] theorem opp2_zero : opp2 (0 : Fin 2) = 1 := rfl

@[simp] theorem opp2_one : opp2 (1 : Fin 2) = 0 := rfl

/-- In `Fin 2`, a colour differs from its opposite. -/
theorem opp2_ne : ∀ i : Fin 2, opp2 i ≠ i := by decide

/-- In `Fin 2`, a colour is the opposite of `j` exactly when it differs from `j`. -/
theorem eq_opp2_iff_ne : ∀ i j : Fin 2, i = opp2 j ↔ i ≠ j := by decide

/-- In `Fin 2`, two colours which differ are opposite. -/
theorem eq_opp2_of_ne : ∀ (i j : Fin 2), i ≠ j → i = opp2 j := by decide

/-- The colour class `i` of the residue of `T`. -/
def cls (T : Finset V) (d : V → Fin 2) (i : Fin 2) : Finset V :=
  (Residue T).filter (fun x => d x = i)

@[simp] theorem mem_cls {T : Finset V} {d : V → Fin 2} {i : Fin 2} {x : V} :
    x ∈ cls T d i ↔ x ∉ T ∧ d x = i := by simp [cls]

/-- A vertex outside `T \ {t}` lies outside `T` or is `t`. -/
theorem notMem_sdiff_singleton {T : Finset V} {t z : V} (hz : z ∉ T \ {t}) :
    z ∉ T ∨ z = t :=
  mem_sdiff_singleton_iff.mp (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩)

/-- **A SINGLE EXTRA VERTEX WITH ALL ITS RESIDUAL NEIGHBOURS IN ONE COLOUR CLASS KEEPS THE
RESIDUE BIPARTITE.**  If every neighbour of `t` lying outside `T` carries the colour `i` of a
proper two-colouring of `G[V \ T]`, then `G[(V \ T) + {t}]` is bipartite: give `t` the colour
`opp2 i`. -/
theorem isBipartite_of_adjIn_mono {T : Finset V} {t : V} (ht : t ∈ T)
    {d : V → Fin 2} (hd : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → d v ≠ d w)
    {i : Fin 2} (hm : ∀ x, G.Adj t x → x ∉ T → d x = i) :
    (deleteFinset G (T \ {t})).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v = t then opp2 i else d v) ?_⟩
  intro v w hadj
  rw [deleteFinset_adj] at hadj
  obtain ⟨hv, hw, hvw⟩ := hadj
  by_cases hvt : v = t
  · have htw : G.Adj t w := hvt ▸ hvw
    have hwt : w ≠ t := fun h => G.irrefl (h ▸ htw)
    have hwT : w ∉ T := by
      rcases notMem_sdiff_singleton hw with h1 | h1
      · exact h1
      · exact absurd h1 hwt
    have hdw : d w = i := hm w htw hwT
    show (if v = t then opp2 i else d v) ≠ (if w = t then opp2 i else d w)
    simp only [hvt, ite_true, hwt, ite_false, hdw]
    exact opp2_ne i
  · have hvT : v ∉ T := (notMem_sdiff_singleton hv).resolve_right hvt
    by_cases hwt : w = t
    · have hwtv : G.Adj t v := (hwt ▸ hvw).symm
      have hdv : d v = i := hm v hwtv hvT
      show (if v = t then opp2 i else d v) ≠ (if w = t then opp2 i else d w)
      simp only [hvt, ite_false, hwt, ite_true, hdv]
      exact fun h => opp2_ne i h.symm
    · have hwT : w ∉ T := (notMem_sdiff_singleton hw).resolve_right hwt
      show (if v = t then opp2 i else d v) ≠ (if w = t then opp2 i else d w)
      simp only [hvt, ite_false, hwt, ite_false]
      exact hd hvT hwT hvw

/-- **A BAD VERTEX OF A TRIANGLE MEETS BOTH COLOUR CLASSES OF THE RESIDUE.** -/
theorem exists_adjIn_color {T : Finset V} {t : V} (ht : t ∈ T)
    {d : V → Fin 2} (hd : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → d v ≠ d w)
    {i : Fin 2} (hb : ¬ (deleteFinset G (T \ {t})).IsBipartite) :
    ∃ x, G.Adj t x ∧ x ∉ T ∧ d x = i := by
  by_contra hc
  refine hb (isBipartite_of_adjIn_mono ht hd (i := opp2 i) fun x hx hxT => ?_)
  have hxn : x ∉ cls T d i := fun h => hc ⟨x, hx, hxT, (mem_cls.mp h).2⟩
  refine eq_opp2_of_ne (i := d x) (j := i) fun h => hxn ?_
  exact mem_cls.mpr ⟨hxT, h⟩

/-! ## Part 2 — BOTH COLOUR CLASSES HAVE TWO ELEMENTS -/

/-- **EACH COLOUR CLASS OF THE RESIDUE OF A TRIANGLE HAS AT LEAST TWO POINTS**, provided every
vertex of the triangle is bad.

A class with no point makes a vertex good (all its residual neighbours carry the other colour), and
a class with a single point is met by all three vertices of the triangle, so that point is adjacent
to all of `T` — which Erdős's hypothesis excludes. -/
theorem card_cls_ge_two (hG : LocIndep 1 G) {T : Finset V} (hT : G.IsNClique 3 T)
    {d : V → Fin 2} (hd : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → d v ≠ d w)
    {i : Fin 2} (hall : ∀ t ∈ T, ∃ x, G.Adj t x ∧ x ∉ T ∧ d x = i)
    (hb : ∀ t ∈ T, ¬ (deleteFinset G (T \ {t})).IsBipartite) :
    2 ≤ (cls T d i).card := by
  have hTc : T.card = 3 := (G.isNClique_iff.mp hT).2
  have hTne : T.Nonempty := Finset.card_ne_zero.mp (by rw [hTc]; decide)
  by_contra hc
  have hle : (cls T d i).card ≤ 1 := by omega
  by_cases hzero : cls T d i = ∅
  · obtain ⟨t, ht⟩ := hTne
    exact hb t ht (isBipartite_of_adjIn_mono ht hd (i := opp2 i) fun x hx hxT => by
      have hxn : x ∉ cls T d i := by
        intro h
        have h2 : x ∈ (∅ : Finset V) := hzero ▸ h
        exact Finset.notMem_empty x h2
      refine eq_opp2_of_ne (i := d x) (j := i) fun h => hxn ?_
      exact mem_cls.mpr ⟨hxT, h⟩)
  · have hne : (cls T d i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    have h1 : (cls T d i).card = 1 := by
      have hcard := Finset.card_ne_zero.mpr hne
      omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hpT : p ∉ T := (mem_cls.mp (by rw [hp]; simp)).1
    have hsub : T ⊆ AdjIn G p T := by
      intro z hz
      obtain ⟨x, hzx, hxT, hxi⟩ := hall z hz
      have hxf : x ∈ cls T d i := mem_cls.mpr ⟨hxT, hxi⟩
      rw [hp] at hxf
      have hxp : x = p := Finset.mem_singleton.mp hxf
      rw [hxp] at hzx
      exact mem_adjIn.mpr ⟨hz, hzx.symm⟩
    have hle' := card_adjIn_le_two_of_isNClique_three hG hT (x := p) hpT
    have hcard := Finset.card_le_card hsub
    exact absurd (show (3 : ℕ) ≤ 2 by omega) (by omega)

