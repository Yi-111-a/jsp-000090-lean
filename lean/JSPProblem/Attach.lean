/-
# JSP-000090 — a clique, the vertices that complete it, and the deficiency

This file is the **sixteenth attack family**.  It works with the *numerical* hypothesis
`MaxDef G ≤ k` of `JSPProblem/Deficiency.lean` and with the one local counting question that the
triangle descent of `JSPProblem/CutTriangle.lean` asks: **how much does a clique, together with the
set of vertices that complete it, contribute to the deficiency?**

Two halves are proved, and one of them is a **machine-checked refutation** of the first concrete
lemma that `discovery/JSP-000090/policy.json` named for the attack on
`JSP90.CutTriangleErdős73`.

## Part 1 (positive) — a clique contributes at most one vertex to any independent set

```lean
JSP90.indepCard_le_one_add_of_isClique :  G.IsClique T → indepCard G (T ∪ X) ≤ 1 + indepCard G X
```

so in the deficiency bookkeeping a clique behaves *additively* with the set of vertices it
dominates (`maxDef_ge_card_add_card_sub_two_add`).  Consequences:

* `maxDef_clique_add_two_le` — a clique has at most `MaxDef G + 2` vertices (the deficiency form of
  `JSP90.LocIndep.clique_card_le`);
* `maxDef_allNeighOf_le` and `maxDef_commonNeigh_le` — the set of vertices completing a clique of
  size `≥ 2` is *deficiency-cheap*: its own deficiency is at most `MaxDef G`, and in particular so
  is the common neighbourhood of an edge;
* **`card_allNeighOf_of_isClique_le`** — *the cliques inside the completion set are bounded*:
  `|T| + |A| ≤ MaxDef G + 2` whenever `T` is a clique and `A` is a clique of vertices each adjacent
  to every vertex of `T` (`isClique_union_allNeighOf`: `T ∪ A` is a clique).  **This is the counting
  lemma the triangle descent actually needs**, and its shape — a bound on the cliques *among* the
  completions rather than on the completions — is forced, see Part 2.

## Part 2 (negative) — the completion sets are **free** in the deficiency

The graph `joinTriangle m = K_3 ∨ I` of `JSPProblem/Attach.lean`, on the vertex type
`Fin 3 × Fin (m + 2)`: the fibre `Fin 3 × {0}` is a triangle, every vertex outside it is adjacent to
all three of its vertices, and there are no other edges.  `maxDef_joinTriangle` proves the **exact**
value

```lean
JSP90.maxDef_joinTriangle : MaxDef (joinTriangle m) = 2      (for every m)
```

— a `K_3` joined to an independent set of arbitrary size has deficiency `2`, because the deficiency
of `T ∪ A` for a clique `T` and completions `A` reads `| T | + | A | - 2 max (1, |A|)`, i.e.
`| T | - | A |` when `A` is independent.  Two cardinality-counting lemmas are therefore **false**,
and both are refuted by the same witness, in the quantified form:

* `completion_card_unbounded` — for every `n` there is a graph with `LocIndep 2` and a triangle
  more than `n` of whose outside vertices are adjacent to all three of its vertices.  This refutes
  *"the vertices completing a triangle to a `K_4` are at most `k - 1`"*, the counting lemma that
  round 65's predecessor proposed as the first step of the attack on
  `JSP90.CutTriangleErdős73`;
* `commonNeigh_card_unbounded` — for every `n` there is a graph with `LocIndep 2` and an edge whose
  common neighbourhood has more than `n` vertices.  This refutes *"the common neighbourhood of an
  edge has at most `k` vertices"*.

So the descent must control the *cliques* among the vertices attached to a clique
(`card_allNeighOf_of_isClique_le`, proved in Part 1) and must handle the remaining, mutually
non-adjacent attachments differently — the same obstruction as `JSP90.absorption_step_fails`
(`JSPProblem/Weight.lean`, witness `K_5`) in the transversal language, and as
`JSP90.card_inter_neigh_le_two` (`JSPProblem/Fan.lean`) in the fan language.

## Environment notes (verified this round)

* `SimpleGraph.IsClique` takes a **`Set`**, while `SimpleGraph.IsIndepSet` also takes a `Set`, but
  `Finset` membership and `Set` membership in the *same* finset are defeq, whereas `↑(insert a s)`
  (finset insert coerced) is **not** defeq to `insert a (↑s)` (`Set.insert`).  Hence: a statement
  `G.IsClique (insert u s)` written at a `Set`-expected position silently becomes a *set* insert,
  and proofs must then use `Set.mem_insert_iff`; `isClique_finset_insert` is the bridge between the
  two forms.  Likewise `G.IsIndepSet (S ∩ T)` written at a `Set`-expected position is a *set*
  intersection, so the finset version has to be ascribed: `G.IsIndepSet ((S ∩ T : Finset V) : Set V)`.
* `SimpleGraph.IsIndepSet_iff` unfolds `Set.Pairwise (fun v w ↦ ¬ G.Adj v w)` to a goal of the form
  `∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ G.Adj x y`, so the fifth binder is the *inequality* and a sixth
  adjacency hypothesis is needed.
* `Finset.mem_insert` on a two-element literal `({a, b} : Finset V)` does not fix the insertion
  order, so it must be normalised first (`by ext x; simp` into `insert a {b}`); `Finset.mem_erase`
  returns `a ≠ b ∧ a ∈ s` in that order, while `Finset.mem_erase_of_mem` is `a ∈ s → a ∉ s → False`.
* `0 : Fin m` needs `NeZero m`, so a witness graph whose parameters range over all `m : ℕ` must use
  a vertex type `Fin 3 × Fin (m + 2)` (and `⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩ : Fin (m + 2)`).
* `omega` treats `indepCard G Y` as an opaque atom **only if the same term (up to instances) occurs
  in the hypotheses**; when the hypothesis and the goal are stated in separate `have`s with different
  elaboration times, `Nat.mul_le_mul_left`/`Nat.add_le_add_left` are more reliable than `omega`.
-/

import JSPProblem.CutTriangle

namespace JSP90

open Finset Fintype Set

noncomputable section

variable {V : Type*} {G : SimpleGraph V} [Fintype V]

local instance : DecidableEq V := Classical.decEq V

local instance (G : SimpleGraph V) : DecidablePred fun S : Finset V => G.IsIndepSet S :=
  fun _ => Classical.propDecidable _

local instance (G : SimpleGraph V) (T : Finset V) :
    DecidablePred (fun v : V => v ∉ T ∧ ∀ w ∈ T, G.Adj v w) := fun _ => Classical.propDecidable _

/-! ## Part 1 — a clique contributes at most one vertex to an independent set -/

section Clique

/-- **The set of vertices that complete `T` to a clique**: the vertices outside `T` adjacent to
*every* vertex of `T`.  For a two-element `T` this is the common neighbourhood of the edge `T`; for
a triangle it is the set of vertices whose addition makes a `K_4`. -/
noncomputable def allNeighOf (G : SimpleGraph V) (T : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter (fun v => v ∉ T ∧ ∀ w ∈ T, G.Adj v w)

theorem mem_allNeighOf {T : Finset V} {v : V} :
    v ∈ allNeighOf G T ↔ v ∉ T ∧ ∀ w ∈ T, G.Adj v w := by
  rw [allNeighOf, Finset.mem_filter]
  simp

/-- The set completing `T` is disjoint from `T`. -/
theorem disjoint_allNeighOf (T : Finset V) : Disjoint T (allNeighOf G T) :=
  Finset.disjoint_left.mpr fun v h1 h2 => (mem_allNeighOf.mp h2).1 h1

/-- **An independent set meets a clique in at most one point**: two distinct points of an
independent set that are both in a clique are impossible. -/
theorem inter_eq_singleton_of_isClique_of_isIndepSet {T S : Finset V} (hT : G.IsClique T)
    (hSi : G.IsIndepSet S) {v : V} (hvT : v ∈ T) (hvS : v ∈ S) {w : V} (hwS : w ∈ S)
    (hwT : w ∈ T) : v = w := by
  by_contra hne
  exact hSi hvS hwS hne (hT hvT hwT hne)

/-- An independent set intersected with a vertex set stays independent. -/
theorem isIndepSet_inter_left {S T : Finset V} (hS : G.IsIndepSet S) :
    G.IsIndepSet ((S ∩ T : Finset V) : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hne
  exact hS (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 hne

/-- **A CLIQUE CONTRIBUTES AT MOST ONE VERTEX TO ANY INDEPENDENT SET.**
`α(G[T ∪ X]) ≤ 1 + α(G[X])` for every clique `T` and every vertex set `X`: an independent set
contained in `X` is already counted, and an independent set meeting `T` has all but one of its
vertices outside `T`, hence in `X`. -/
theorem indepCard_le_one_add_of_isClique {T X : Finset V} (hT : G.IsClique T) :
    indepCard G (T ∪ X) ≤ 1 + indepCard G X := by
  refine Finset.sup_le_iff.mpr fun S hS => ?_
  have hsub : S ⊆ T ∪ X := sub_of_mem_indepSets hS
  have hSi : G.IsIndepSet S := (Finset.mem_filter.mp hS).2
  by_cases hSX : S ⊆ X
  · have hle : S.card ≤ indepCard G X := le_indepCard_of_isIndepSet hSX hSi
    omega
  · obtain ⟨v, hvS, hvX⟩ := Finset.not_subset.mp hSX
    have hvT : v ∈ T := by
      rcases Finset.mem_union.mp (hsub hvS) with h | h
      · exact h
      · exact absurd h hvX
    have herase : S.erase v ⊆ X := by
      intro w hw
      rw [Finset.mem_erase] at hw
      rcases Finset.mem_union.mp (hsub hw.2) with hT' | hX'
      · exact absurd (inter_eq_singleton_of_isClique_of_isIndepSet hT hSi hvT hvS hw.2 hT') (Ne.symm hw.1)
      · exact hX'
    have hSiE : G.IsIndepSet (S.erase v) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne
      exact hSi (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp hb).2 hne
    have hle : (S.erase v).card ≤ indepCard G X :=
      le_indepCard_of_isIndepSet herase hSiE
    have hcard : S.card = (S.erase v).card + 1 := (Finset.card_erase_add_one hvS).symm
    omega

/-- **THE ADDITIVE FORM OF THE CLAUSE.**  If `T` is a clique disjoint from `X`, then the deficiency
of `T ∪ X` is at least `( |T| + |X| ) - 2 - 2 α(G[X])`: the clique costs `|T|` vertices and buys
one vertex of the independent set.  Phrased linearly, so that the truncation at zero of `Nat`
subtraction cannot interfere. -/
theorem maxDef_ge_card_add_card_sub_two_add {T X : Finset V} (hT : G.IsClique T)
    (hTX : Disjoint T X) :
    T.card + X.card - 2 * (1 + indepCard G X) ≤ MaxDef G := by
  have h1 : defOf G (T ∪ X) ≤ MaxDef G := le_maxDef G (T ∪ X)
  have h2 : indepCard G (T ∪ X) ≤ 1 + indepCard G X := indepCard_le_one_add_of_isClique hT
  have h3 : (T ∪ X).card - 2 * (1 + indepCard G X) ≤ defOf G (T ∪ X) := by
    have hsub : 2 * indepCard G (T ∪ X) ≤ 2 * (1 + indepCard G X) := by omega
    exact Nat.sub_le_sub_left hsub (T ∪ X).card
  have h4 : (T ∪ X).card = T.card + X.card := Finset.card_union_of_disjoint hTX
  omega

/-- **A CLIQUE HAS AT MOST `MaxDef G + 2` VERTICES**, the deficiency form of
`JSP90.LocIndep.clique_card_le`. -/
theorem maxDef_clique_add_two_le {T : Finset V} (hT : G.IsClique T) :
    T.card ≤ MaxDef G + 2 := by
  have hdisj : Disjoint T (∅ : Finset V) :=
    Finset.disjoint_left.mpr fun _ _ h => absurd h (by simp)
  have h1 := maxDef_ge_card_add_card_sub_two_add hT hdisj
  simp only [indepCard_empty, Finset.card_empty, add_zero, mul_one] at h1
  rw [Nat.sub_le_iff_le_add] at h1
  omega

/-- **THE SET COMPLETING A CLIQUE IS DEFICIENT BY AT MOST `MaxDef G`.**  In words: the vertices
that complete a clique `T` (of size at least `2`) to a bigger clique cost, in deficiency, no more
than the whole graph — and the bound is *additive*: the clique and the deficiency of the completion
set are accounted for separately.  This is the quantitative form of the observation that a vertex
completing a clique is not free, while `r` mutually non-adjacent such vertices cost nothing at all
(see `Part 2`). -/
theorem maxDef_allNeighOf_le {T : Finset V} (hT : G.IsClique T) (h2 : 2 ≤ T.card) :
    defOf G (allNeighOf G T) ≤ MaxDef G := by
  have h1 := maxDef_ge_card_add_card_sub_two_add hT (X := allNeighOf G T) (disjoint_allNeighOf T)
  rw [Nat.sub_le_iff_le_add] at h1
  simp only [defOf]
  rw [Nat.sub_le_iff_le_add]
  omega

/-- **THE UNION OF A CLIQUE AND A CLIQUE OF ITS COMPLETIONS IS A CLIQUE.**  Every point of `A` is
adjacent to every point of `T` by `A ⊆ allNeighOf G T`, and `A` is a clique. -/
theorem isClique_union_allNeighOf {T A : Finset V} (hT : G.IsClique T) (hA : G.IsClique A)
    (hmem : A ⊆ allNeighOf G T) : G.IsClique (↑(T ∪ A) : Set V) := by
  intro x hx y hy hxy
  have hx' : x ∈ (T ∪ A : Finset V) := hx
  have hy' : y ∈ (T ∪ A : Finset V) := hy
  rcases Finset.mem_union.mp hx' with hxT | hxA
  · rcases Finset.mem_union.mp hy' with hyT | hyA
    · exact hT hxT hyT hxy
    · exact (G.adj_symm ((mem_allNeighOf.mp (hmem hyA)).2 x hxT))
  · rcases Finset.mem_union.mp hy' with hyT | hyA
    · exact (mem_allNeighOf.mp (hmem hxA)).2 y hyT
    · exact hA hxA hyA hxy

/-- **THE CLINIQUES INSIDE THE COMPLETION SET ARE BOUNDED — THIS IS THE COUNTING LEMMA THE
TRIANGLE DESCENT ACTUALLY NEEDS.**  If `A` is a clique of vertices each adjacent to every vertex of
a clique `T`, then `T ∪ A` is a clique of `G`, so `|T| + |A| ≤ MaxDef G + 2`.  Note the shape: a
bound on the *cliques* among the completions, not on the completions themselves — `Part 2` shows
that no bound on the latter exists. -/
theorem card_allNeighOf_of_isClique_le {T A : Finset V} (hT : G.IsClique T) (hA : G.IsClique A)
    (hmem : A ⊆ allNeighOf G T) : T.card + A.card ≤ MaxDef G + 2 := by
  have hcl := isClique_union_allNeighOf hT hA hmem
  have h1 := maxDef_clique_add_two_le (T := T ∪ A) hcl
  rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun v h1 h2 =>
    (mem_allNeighOf.mp (hmem h2)).1 h1)] at h1
  exact h1

/-- **THE TWO ENDS OF AN EDGE SPAN A CLIQUE.** -/
theorem isClique_pair {a b : V} (hab : G.Adj a b) :
    G.IsClique (↑({a, b} : Finset V) : Set V) := by
  have hset : ({a, b} : Finset V) = insert a {b} := by ext x; simp
  intro x hx y hy hxy
  have hx' : x ∈ ({a, b} : Finset V) := hx
  have hy' : y ∈ ({a, b} : Finset V) := hy
  rw [hset] at hx' hy'
  rcases Finset.mem_insert.mp hx' with hxa | hxb
  · rcases Finset.mem_insert.mp hy' with hya | hyb
    · exact (hxy (hxa.trans hya.symm)).elim
    · rw [hxa, Finset.mem_singleton.mp hyb]
      exact hab
  · have hxb' : x = b := Finset.mem_singleton.mp hxb
    rcases Finset.mem_insert.mp hy' with hya | hyb
    · rw [hxb', hya]
      exact G.adj_symm hab
    · exact (hxy (hxb'.trans (Finset.mem_singleton.mp hyb).symm)).elim

/-- **THE COMMON NEIGHBOURHOOD OF AN EDGE HAS DEFICIENCY AT MOST `MaxDef G`.** -/
theorem maxDef_commonNeigh_le {a b : V} (hab : G.Adj a b) :
    defOf G (allNeighOf G {a, b}) ≤ MaxDef G := by
  have hne : a ≠ b := fun h => G.irrefl (h ▸ hab)
  have hcl : G.IsClique (↑({a, b} : Finset V) : Set V) := isClique_pair hab
  have hcard : ({a, b} : Finset V).card = 2 := by
    rw [show ({a, b} : Finset V) = insert a {b} from by ext x; simp,
      Finset.card_insert_of_notMem (s := ({b} : Finset V))
        (fun h2 => hne (Finset.mem_singleton.mp h2)),
      Finset.card_singleton]
  refine maxDef_allNeighOf_le (T := ({a, b} : Finset V)) hcl ?_
  rw [hcard]

/-- **THE LOCAL COUNTING QUESTION OF THE TRIANGLE DESCENT, IN THE RIGHT VOCABULARY.**  The
completion set of a clique is *deficiency-cheap* (at most `MaxDef G`), and the cliques inside it
are bounded (`card_allNeighOf_of_isClique_le`); `Part 2` shows that no cardinality bound on the
completion set itself exists. -/
theorem allNeighOf_defOf_le_of_isClique {T : Finset V} (hT : G.IsClique T) (h2 : 2 ≤ T.card) :
    defOf G (allNeighOf G T) ≤ MaxDef G :=
  maxDef_allNeighOf_le hT h2

end Clique

/-! ## Part 2 — the cardinalities are **not** bounded: `K_3 ∨ I`

The deficiency of a clique `T` together with a set `A` of vertices each adjacent to *every* vertex
of `T` reads

```
| T ∪ A | - 2 α(G[T ∪ A])  =  | T | + | A | - 2 max (1, |A|)
```

because a clique meets an independent set in at most one point, and a point of `T` is adjacent to
every point of `A`.  So the deficiency is `| T | - | A |` when `A` is independent: **the completion
set is free in the deficiency**, and `K_3 ∨ I_m` has deficiency `2` for every `m`.  Both
cardinality lemmas that the descent would like are therefore false, and the theorems
`completion_card_unbounded` / `commonNeigh_card_unbounded` refute them with the same witness. -/

section JoinTriangle

variable {m : ℕ}

local instance : DecidableEq (Fin 3 × Fin (m + 2)) := Classical.decEq _
local instance : DecidableEq (Finset (Fin 3 × Fin (m + 2))) := Classical.decEq _

/-- **`K_3 ∨ I_m`: a triangle joined to an independent set of `m` vertices.**  The triangle is the
fibre `Fin 3 × {0}`; every vertex outside it is adjacent to all three of its vertices, and there
are no other edges, so the vertices outside the triangle form an independent set. -/
def joinTriangle (m : ℕ) : SimpleGraph (Fin 3 × Fin (m + 2)) where
  Adj p q := (p.2 = 0 ∧ q.2 = 0 ∧ p.1 ≠ q.1) ∨ (p.2 = 0 ∧ q.2 ≠ 0) ∨ (p.2 ≠ 0 ∧ q.2 = 0)
  symm := ⟨fun _ _ h => by
    rcases h with h | h | h
    · exact Or.inl ⟨h.2.1, h.1, fun hc => h.2.2 hc.symm⟩
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨fun _ h => by
    rcases h with h | h | h
    · exact h.2.2 rfl
    · exact h.2 h.1
    · exact h.1 h.2⟩

@[simp] theorem joinTriangle_adj {p q : Fin 3 × Fin (m + 2)} :
    (joinTriangle m).Adj p q ↔
      (p.2 = 0 ∧ q.2 = 0 ∧ p.1 ≠ q.1) ∨ (p.2 = 0 ∧ q.2 ≠ 0) ∨ (p.2 ≠ 0 ∧ q.2 = 0) :=
  Iff.rfl

/-- The triangle of `joinTriangle m`: the fibre `Fin 3 × {0}`, of size `3`. -/
def joinTriangle_tri (m : ℕ) : Finset (Fin 3 × Fin (m + 2)) :=
  (Finset.univ : Finset (Fin 3)).image fun a : Fin 3 => (a, 0)

theorem mem_joinTriangle_tri {p : Fin 3 × Fin (m + 2)} : p ∈ joinTriangle_tri m ↔ p.2 = 0 := by
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact (congrArg Prod.snd ha).symm
  · intro h
    exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl h.symm⟩

theorem card_joinTriangle_tri (m : ℕ) : (joinTriangle_tri m).card = 3 := by
  have hinj : Function.Injective (fun a : Fin 3 => (a, (0 : Fin (m + 2)))) := by
    intro a b h
    exact congrArg Prod.fst h
  have h1 : (joinTriangle_tri m).card = (Finset.univ : Finset (Fin 3)).card := by
    unfold joinTriangle_tri
    exact Finset.card_image_of_injective _ hinj
  rw [h1]
  simp

/-- **The vertices outside the triangle**: an independent set of size exactly `m`. -/
def joinTriangle_tail (m : ℕ) : Finset (Fin 3 × Fin (m + 2)) :=
  ((Finset.univ : Finset (Fin (m + 2))).filter (fun i : Fin (m + 2) => i ≠ 0)).image
    fun i : Fin (m + 2) => ((0 : Fin 3), i)

theorem mem_joinTriangle_tail {p : Fin 3 × Fin (m + 2)} :
    p ∈ joinTriangle_tail m ↔ p.1 = 0 ∧ p.2 ≠ 0 := by
  constructor
  · intro h
    obtain ⟨i, hi, hi2⟩ := Finset.mem_image.mp h
    have hne : i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hp2 : p.2 ≠ 0 := by
      intro hc
      have h1 : i = p.2 := by simpa using (congrArg Prod.snd hi2)
      rw [hc] at h1
      exact hne h1
    have hp1 : p.1 = 0 := by
      have h1 : (0 : Fin 3) = p.1 := by simpa using (congrArg Prod.fst hi2)
      exact h1.symm
    exact ⟨hp1, hp2⟩
  · rintro ⟨hp1, hp2⟩
    exact Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2⟩,
      Prod.ext hp1.symm rfl⟩

theorem card_joinTriangle_tail (m : ℕ) : (joinTriangle_tail m).card = m + 1 := by
  have hset : ((Finset.univ : Finset (Fin (m + 2))).filter (fun i : Fin (m + 2) => i ≠ 0))
      = (Finset.univ : Finset (Fin (m + 2))).erase 0 := by
    ext i
    constructor
    · intro h
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp h).2, Finset.mem_univ _⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_erase.mp h).1⟩
  have hinj : Function.Injective (fun i : Fin (m + 2) => ((0 : Fin 3), i)) :=
    fun _ _ h => congrArg Prod.snd h
  have hcard : ((Finset.univ : Finset (Fin (m + 2))).filter
      (fun i : Fin (m + 2) => i ≠ 0)).card =
      ((Finset.univ : Finset (Fin (m + 2))).erase 0).card := by rw [hset]
  have h2 : (joinTriangle_tail m).card = ((Finset.univ : Finset (Fin (m + 2))).filter
      (fun i : Fin (m + 2) => i ≠ 0)).card := by
    unfold joinTriangle_tail
    exact Finset.card_image_of_injective _ hinj
  have hmem : (0 : Fin (m + 2)) ∈ (Finset.univ : Finset (Fin (m + 2))) := Finset.mem_univ _
  rw [h2, hcard, Finset.card_erase_of_mem hmem]
  simp

/-- The triangle is a clique. -/
theorem isClique_joinTriangle_tri (m : ℕ) :
    (joinTriangle m).IsClique (joinTriangle_tri m) := by
  intro x hx y hy hxy
  exact joinTriangle_adj.mpr (Or.inl ⟨mem_joinTriangle_tri.mp hx, mem_joinTriangle_tri.mp hy,
    fun hc => (hxy (Prod.ext hc ((mem_joinTriangle_tri.mp hx).trans
      (mem_joinTriangle_tri.mp hy).symm))).elim⟩)

/-- **A clique hypothesis survives the passage from a finset to the set it coerces to**: the two
readiness conditions of `SimpleGraph.IsClique` only differ in the form of the membership statement. -/
theorem isClique_finset_insert {G : SimpleGraph V} {u : V} {s : Finset V}
    (h : G.IsClique (insert u (s : Set V))) : G.IsClique ((insert u s : Finset V) : Set V) := by
  have heq : insert u (s : Set V) = ((insert u s : Finset V) : Set V) := by
    ext x
    simp
  rw [← heq]
  exact h

/-- **A COMPLETION OF THE TRIANGLE EXTENDS IT TO A `K_4`.** -/
theorem isClique_tri_insert (m : ℕ) (u : Fin 3 × Fin (m + 2)) (hu : u.2 ≠ 0) :
    (joinTriangle m).IsClique (insert u (joinTriangle_tri m)) := by
  intro x hx y hy hxy
  rw [Set.mem_insert_iff] at hx
  rw [Set.mem_insert_iff] at hy
  rcases hx with hxu | hx
  · rcases hy with hyu | hy
    · exact (hxy (hxu.trans hyu.symm)).elim
    · rw [hxu]
      exact joinTriangle_adj.mpr (Or.inr (Or.inr ⟨hu, mem_joinTriangle_tri.mp hy⟩))
  · rcases hy with hyu | hy
    · rw [hyu]
      exact joinTriangle_adj.mpr (Or.inr (Or.inl ⟨mem_joinTriangle_tri.mp hx, hu⟩))
    · exact joinTriangle_adj.mpr (Or.inl ⟨mem_joinTriangle_tri.mp hx, mem_joinTriangle_tri.mp hy,
        fun hc => (hxy (Prod.ext hc ((mem_joinTriangle_tri.mp hx).trans
      (mem_joinTriangle_tri.mp hy).symm))).elim⟩)

/-- **Two vertices outside the triangle are never adjacent**: they form an independent set. -/
theorem isIndepSet_joinTriangle_tail (m : ℕ) :
    (joinTriangle m).IsIndepSet (joinTriangle_tail m) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro p hp q hq hne hadj
  obtain ⟨_, hp2⟩ := mem_joinTriangle_tail.mp hp
  obtain ⟨_, hq2⟩ := mem_joinTriangle_tail.mp hq
  rcases joinTriangle_adj.mp hadj with h | h | h
  · exact absurd h.1 hp2
  · exact absurd h.1 hp2
  · exact absurd h.2 hq2

/-- **Everything outside the triangle is an independent set.**  This is the counting set of
`maxDef_le_two_joinTriangle`: `| Y | ≤ | Y \ tri | + 3` for every vertex set `Y`, and
`Y \ tri` is independent. -/
theorem isIndepSet_joinTriangle_sdiff (m : ℕ) (Y : Finset (Fin 3 × Fin (m + 2))) :
    (joinTriangle m).IsIndepSet ((Y \ (joinTriangle_tri m) : Finset (Fin 3 × Fin (m + 2))) : Set _) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro p hp q hq hne hadj
  obtain ⟨hpY, hpT⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hqY, hqT⟩ := Finset.mem_sdiff.mp hq
  have hp2 : p.2 ≠ 0 := fun hc => hpT (mem_joinTriangle_tri.mpr hc)
  have hq2 : q.2 ≠ 0 := fun hc => hqT (mem_joinTriangle_tri.mpr hc)
  rcases joinTriangle_adj.mp hadj with h | h | h
  · exact absurd h.1 hp2
  · exact absurd h.1 hp2
  · exact absurd h.2 hq2

/-- **Every vertex outside the triangle is adjacent to all three of its vertices.** -/
theorem adj_of_tail_tri {p q : Fin 3 × Fin (m + 2)} (hp2 : p.2 ≠ 0) (hq : q.2 = 0) :
    (joinTriangle m).Adj p q :=
  joinTriangle_adj.mpr (Or.inr (Or.inr ⟨hp2, hq⟩))

/-! ### The exact deficiency of `K_3 ∨ I_m` is `2`, for every `m` -/

/-- **The arithmetic of the deficiency bound**: one point of independence buys two vertices, so a
vertex set with `r` independent points and at most `s` further (clique-like) points has deficiency
at most `r + s - 2 r`. -/
theorem add_three_le_two_add_two_of_one_le {r : ℕ} (h : 1 ≤ r) : r + 3 ≤ 2 + 2 * r := by omega

/-- ... and the case of at most one independent point: `| Y | ≤ 4`, so one point of independence
suffices to bring the deficiency down to `4 - 2 = 2`. -/
theorem le_four_of_le_add_one {r : ℕ} (h : r ≤ 1) : r + 3 ≤ 4 := by omega

/-- **Every vertex set of `joinTriangle m` has deficiency at most `2`.**  The independent sets of
`G[Y]` either avoid the triangle part — then they live in `Y ∩ tail`, which is independent — or
consist of a single point; and `| Y | ≤ | Y ∩ tail | + 3` always. -/
theorem maxDef_le_two_joinTriangle (m : ℕ) : MaxDef (joinTriangle m) ≤ 2 := by
  refine maxDef_le fun Y => ?_
  rw [defOf, Nat.sub_le_iff_le_add]
  have hcard : Y.card ≤ (Y \ (joinTriangle_tri m)).card + 3 := by
    have hsub : Y ⊆ (Y ∩ (joinTriangle_tri m)) ∪ (Y \ (joinTriangle_tri m)) := by
      intro v hv
      by_cases htri : v.2 = 0
      · have h1 : v ∈ Y ∩ (joinTriangle_tri m) :=
          Finset.mem_inter.mpr ⟨hv, mem_joinTriangle_tri.mpr htri⟩
        exact Finset.mem_union_left _ h1
      · have h1 : v ∈ Y \ (joinTriangle_tri m) := Finset.mem_sdiff.mpr
          ⟨hv, fun hc => htri (mem_joinTriangle_tri.mp hc)⟩
        exact Finset.mem_union_right _ h1
    calc Y.card ≤ ((Y ∩ (joinTriangle_tri m)) ∪ (Y \ (joinTriangle_tri m))).card :=
          Finset.card_le_card hsub
      _ ≤ (Y ∩ (joinTriangle_tri m)).card + (Y \ (joinTriangle_tri m)).card :=
          Finset.card_union_le _ _
      _ ≤ (Y \ (joinTriangle_tri m)).card + 3 := by
          have h1 : (Y ∩ (joinTriangle_tri m)).card ≤ (joinTriangle_tri m).card :=
            Finset.card_le_card Finset.inter_subset_right
          rw [card_joinTriangle_tri] at h1
          omega
  by_cases hsmall : (Y \ (joinTriangle_tri m)).card ≤ 1
  · by_cases hne : Y.Nonempty
    · have h1 : Y.card ≤ 4 := le_trans hcard (le_four_of_le_add_one hsmall)
      have hα : 1 ≤ indepCard (joinTriangle m) Y := Nat.succ_le_of_lt (indepCard_pos hne)
      calc Y.card ≤ 4 := h1
        _ = 2 + 2 := by omega
        _ ≤ 2 + 2 * indepCard (joinTriangle m) Y :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 hα) 2
    · have hY : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hY, Finset.card_empty, indepCard_empty]
      exact Nat.zero_le _
  · have hα : 1 ≤ (Y \ (joinTriangle_tri m)).card := by omega
    have hSi : (joinTriangle m).IsIndepSet
        ((Y \ (joinTriangle_tri m) : Finset (Fin 3 × Fin (m + 2))) : Set _) :=
      isIndepSet_joinTriangle_sdiff m Y
    have hle : (Y \ (joinTriangle_tri m)).card ≤ indepCard (joinTriangle m) Y :=
      le_indepCard_of_isIndepSet (Finset.sdiff_subset.trans Finset.Subset.rfl) hSi
    have h2 : (Y \ (joinTriangle_tri m)).card + 3
        ≤ 2 + 2 * (Y \ (joinTriangle_tri m)).card :=
      add_three_le_two_add_two_of_one_le hα
    calc Y.card ≤ (Y \ (joinTriangle_tri m)).card + 3 := hcard
      _ ≤ 2 + 2 * (Y \ (joinTriangle_tri m)).card := h2
      _ ≤ 2 + 2 * indepCard (joinTriangle m) Y := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hle) 2

/-- `K_3 ∨ I_m` has deficiency at least `2`: the triangle together with one of its completions is a
`K_4`, whose deficiency is `4 - 2 = 2`. -/
theorem maxDef_joinTriangle_two (m : ℕ) : 2 ≤ MaxDef (joinTriangle m) := by
  have hcl := isClique_tri_insert m ((0 : Fin 3), ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩) (by simp)
  have h1 : defOf (joinTriangle m)
      (insert ((0 : Fin 3), ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩) (joinTriangle_tri m)) ≤ MaxDef (joinTriangle m) :=
    le_maxDef _ _
  have hα : indepCard (joinTriangle m)
      (insert ((0 : Fin 3), ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩) (joinTriangle_tri m)) = 1 :=
    indepCard_eq_one_of_clique
      ⟨(0, ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩), Finset.mem_insert_self _ _⟩
      (isClique_finset_insert hcl)
  have hcard : (insert ((0 : Fin 3), ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩) (joinTriangle_tri m)).card = 4 := by
    have hnm : ((0 : Fin 3), ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩)
        ∉ joinTriangle_tri m := fun h =>
      absurd (mem_joinTriangle_tri.mp h) (by simp)
    rw [Finset.card_insert_of_notMem hnm, card_joinTriangle_tri]
  rw [defOf, hcard, hα] at h1
  omega

/-- **THE EXACT VALUE OF THE DEFICIENCY OF `K_3 ∨ I_m` IS `2`, INDEPENDENT OF `m`.** -/
theorem maxDef_joinTriangle (m : ℕ) : MaxDef (joinTriangle m) = 2 :=
  le_antisymm (maxDef_le_two_joinTriangle m) (maxDef_joinTriangle_two m)

theorem locIndep_two_joinTriangle (m : ℕ) : LocIndep 2 (joinTriangle m) :=
  locIndep_of_maxDef_le (maxDef_joinTriangle m).le

/-- **THE `K_4`-COMPLETIONS OF A TRIANGLE ARE NOT COUNTED BY THE DEFICIENCY.**
For every `n` there is a graph satisfying `LocIndep 2` together with a triangle more than `n` of
whose outside vertices are adjacent to all three of its vertices.  This refutes the counting lemma
"the vertices completing a triangle to a `K_4` are at most `k - 1`", which
`discovery/JSP-000090/policy.json` named as the first concrete lemma of the attack on
`JSP90.CutTriangleErdős73`; the deficiency of `K_3 ∨ I_n` is `2` for every `n`. -/
theorem completion_card_unbounded (n : ℕ) :
    ∃ (G : SimpleGraph (Fin 3 × Fin (n + 2))), LocIndep 2 G ∧
      ∃ T : Finset (Fin 3 × Fin (n + 2)), G.IsClique T ∧ T.card = 3 ∧
        n < (allNeighOf G T).card := by
  refine ⟨joinTriangle n, locIndep_two_joinTriangle n, joinTriangle_tri n,
    isClique_joinTriangle_tri n, card_joinTriangle_tri n, ?_⟩
  have hsub : joinTriangle_tail n
      ⊆ allNeighOf (joinTriangle n) (joinTriangle_tri n) := by
    intro v hv
    rw [mem_allNeighOf]
    obtain ⟨hv1, hv2⟩ := mem_joinTriangle_tail.mp hv
    have hm : v ∉ (joinTriangle_tri n : Finset _) := by
      rw [mem_joinTriangle_tri]
      exact hv2
    refine ⟨hm, ?_⟩
    intro w hw
    have hw2 : w.2 = 0 := mem_joinTriangle_tri.mp hw
    exact adj_of_tail_tri hv2 hw2
  show n < (allNeighOf (joinTriangle n) (joinTriangle_tri n)).card
  calc n < n + 1 := by omega
    _ = (joinTriangle_tail n).card := (card_joinTriangle_tail n).symm
    _ ≤ (allNeighOf (joinTriangle n) (joinTriangle_tri n)).card := Finset.card_le_card hsub

/-- **THE COMMON NEIGHBOURHOOD OF AN EDGE IS NOT COUNTED BY THE DEFICIENCY EITHER.**
For every `n` there is a graph satisfying `LocIndep 2` together with an edge whose common
neighbourhood has more than `n` vertices.  This refutes "the common neighbourhood of an edge has
at most `k` vertices", by the same witness. -/
theorem commonNeigh_card_unbounded (n : ℕ) :
    ∃ (G : SimpleGraph (Fin 3 × Fin (n + 2))), LocIndep 2 G ∧
      ∃ a b : Fin 3 × Fin (n + 2), G.Adj a b ∧
        n < (allNeighOf G ({a, b} : Finset (Fin 3 × Fin (n + 2)))).card := by
  refine ⟨joinTriangle n, locIndep_two_joinTriangle n, (0, 0), (1, 0), ?_, ?_⟩
  · exact joinTriangle_adj.mpr (Or.inl ⟨rfl, rfl, show (0 : Fin 3) ≠ 1 by decide⟩)
  · have hsub : joinTriangle_tail n
        ⊆ allNeighOf (joinTriangle n) ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2))) := by
      intro v hv
      rw [mem_allNeighOf]
      obtain ⟨hv1, hv2⟩ := mem_joinTriangle_tail.mp hv
      have hm : v ∉ ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2))) := by
        have hset : ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2))) = insert (0, 0) {(1, 0)} := by
          ext x; simp
        rw [hset, Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl)
        · exact hv2 (by simp)
        · exact hv2 (by simp)
      refine ⟨hm, ?_⟩
      intro w hw
      have hw' : w ∈ ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2))) := hw
      rw [show ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2))) = insert (0, 0) {(1, 0)}
        from by ext x; simp] at hw'
      rcases Finset.mem_insert.mp hw' with h | h
      · have h2 : w.2 = 0 := by simpa using congrArg Prod.snd h
        exact adj_of_tail_tri hv2 h2
      · have h2 : w.2 = 0 := by
          rw [Finset.mem_singleton.mp h]
        exact adj_of_tail_tri hv2 h2
    show n < (allNeighOf (joinTriangle n) ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2)))).card
    calc n < n + 1 := by omega
      _ = (joinTriangle_tail n).card := (card_joinTriangle_tail n).symm
      _ ≤ (allNeighOf (joinTriangle n)
          ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin (n + 2)))).card :=
        Finset.card_le_card hsub

end JoinTriangle

end

end JSP90
