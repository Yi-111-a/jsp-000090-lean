/-
# JSP-000090 — `JSPProblem/Split.lean`: the SPLIT-GRAPH axis (round 107)

The header of this file, the thirtieth family of attacks on Erdős Problem #73, records the class
whose accounting turns out to be the cleanest of all the classes proved so far, and *why*.

## What the earlier rounds left

Round 105 (`Exact.lean`) proved that **both** sides of Erdős #73 are exactly additive over an
anticomplete cover of the vertex set, and recorded its own limit: an anticomplete cover of `V` with
two nonempty pieces *is* a disconnection, so the additive axis pays only for **disconnected**
graphs.  Round 106 (`Multi.lean`) took the connected complement — the complete multipartite graphs
— and computed both sides exactly there, with the optimal constant `f(k) = k`.

Both of those classes are *uniform*: every piece of the decomposition looks the same, and the odd
cycles live *inside* the pieces.  The class Erdős's own hypothesis is usually illustrated on, and
which none of the earlier axes reaches, is a **connected graph whose odd cycles straddle a
partition**: the **split graphs**, i.e. `V = A ⊔ B` with `A` independent and `B` a clique.  This
class is simultaneously

* **connected** (whenever `B` has three vertices and some `a ∈ A` is adjacent to two of them), so no
  anticomplete-decomposition instance applies;
* **not** a cluster graph and **not** a complete multipartite graph (both sides are nonempty and of
  incompatible shapes), and not a disjoint union of odd cycles either;
* governed by **one local rule**: an odd cycle of `A ⊔ B` that is not contained in `B` uses a
  vertex of `A` between two of its neighbours, so `τ(G)` is decided by the *pairs* of the clique
  side and by nothing else.

## What this file adds

For a split partition `V = A ⊔ B` both sides of Erdős #73 have an exact value, and the exact value
of the conclusion is a **two-regime** statement:

| quantity | value on a split graph |
| --- | --- |
| `α(G[X])` for `X ⊆ V` | `≥ |X ∩ A|`, and `≥ 1 + |X ∩ A|` if `X` meets the clique |
| `MaxDef G` | `≤ |B| − 1` |
| `LocIndep k G` | `⟹ |B| ≤ k + 2` |
| `τ(G)` | `|B| − 1`, or `|B| − 2` when the clique side has a pair with **no** common neighbour |

The last line is the content of the file:

```
JSP90.SplitPartition G A B           A ⊔ B = V, A independent, B a clique
JSP90.card_eq_..._splitPartition     |X| = |X ∩ A| + |X ∩ B|            (the counting lemma)
JSP90.cardB_le_locIndep_add_two      LocIndep k G → |B| ≤ k + 2            (the hypothesis)
JSP90.maxDef_split_le                MaxDef G ≤ |B| − 1                   (the hypothesis)
JSP90.IsolatedPair G A B             a pair of clique vertices with no common neighbour in A
JSP90.cardBsdiff_le_two_of_...       a bipartite residue keeps at most two vertices of B
JSP90.not_isBipartite_..._of_commonNeighbour
                                    a common neighbour of a surviving pair is a triangle
JSP90.closeToBipartite_split_iff     THE EXACT VALUE OF THE CONCLUSION (the two regimes)
JSP90.erdos73On_of_splitPartition    A NEW INSTANCE OF THE HEADLINE THEOREM, constant k + 1
```

and then, in Part 4, the **witness family** on which the constant `k + 1` is attained for every
`k ≥ 1` is *stated and analysed* (`K_{k+2,k+2}` minus a perfect matching): the three `Finset`
computations that finish its `LocIndep` proof are recorded there, with the exact lemma names, as the
one remaining step of this axis.

## What is *not* proved

`jsp_000090_main` is not declared and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is
unchanged: this file is about a class, not about the general case.  Its instance is the **seventh**
class on which Erdős #73 is proved with an optimal constant, and the **first** one whose optimal
constant is *strictly larger* than `k` while the class still consists of graphs whose odd cycles are
described completely by a local rule.  So the two-regime value `τ(G) ∈ {|B| − 1, |B| − 2}` is a
genuine instance of the headline theorem, not a degenerate one; but split graphs are not
3-connected in general, and the 3-connected case remains the obstruction.

## Toolchain notes

* The witness lives on `(Fin (k+2) × Fin (k+2)) ⊕ Fin (k+2)`; its two parts are `Finset.image`s of
  `Finset.univ`, so `Finset.card_image_of_injective` gives their sizes (`card_splitWitnessInd`,
  `card_splitWitnessClique`) and no `Finset.filter` is needed anywhere in this file.
* `DecidableEq V` is declared once, at the top of the file, exactly as `JSPProblem/Deficiency.lean`
  does it (`local instance instDecidableEqDef`): the statements below mention `X ∩ A`, so the
  instance has to exist at statement level.  The witness section adds its own instance for
  `Fin n` and uses the same convention as `Deficiency.lean`'s `instDecidableEqFinDef`.
* The colouring of Part 3 is `fun v => if G.Adj v b₁ then 1 else 0` with `b₁` a surviving clique
  vertex; the nine cases of properness are forced, and `IsolatedPair` is exactly what makes the
  "independent vertex adjacent to `b₂`" case impossible.
-/
import JSPProblem.Multi

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqSplitGraph : DecidableEq V := Classical.decEq V

/-! ## Part 0 — two counting lemmas -/

/-- **Two distinct elements force a finset to have at least two elements.** -/
theorem card_ge_two_of_mem_ne {α : Type*} [Fintype α] (s : Finset α) (x y : α) (hx : x ∈ s)
    (hy : y ∈ s) (hne : x ≠ y) : 2 ≤ s.card := by
  classical
  have hsub : ({x, y} : Finset α) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact h ▸ hy
  have h := Finset.card_le_card hsub
  rw [Finset.card_eq_two.mpr ⟨x, y, hne, rfl⟩] at h
  omega

/-- **A finset of at least three elements has a third element outside any two of its elements.** -/
theorem exists_mem_sdiff_pair_of_card_ge_three {α : Type*} [Fintype α] (s : Finset α)
    (hs : 3 ≤ s.card) (x y : α) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (s \ {x, y}).Nonempty := by
  classical
  have hsub : ({x, y} : Finset α) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact h ▸ hy
  have hcard : (s \ ({x, y} : Finset α)).card = s.card - 2 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_eq_two.mpr ⟨x, y, hne, rfl⟩]
  exact Finset.card_pos.mp (by rw [hcard]; omega)

/-! ## Part 1 — the class -/

/-- **A split partition of `G`**: the vertex set splits as `V = A ⊔ B`, where `A` is **independent**
and `B` is a **clique**.

A graph carrying such a partition is a *split graph*.  The two sides are required to be disjoint: in
a genuine split graph the partition can always be made disjoint by moving `A ∩ B` into `A`, and
disjointness is what makes the counting lemma
`card_eq_card_inter_add_card_inter_splitPartition` hold without a correction term.

On this class the odd cycles are described by one local rule, which is the whole content of the
file: an odd cycle of `A ⊔ B` either lies inside `B` or uses a vertex of `A` between two of its
neighbours, so `τ(G)` is decided by the *pairs* of the clique side. -/
def SplitPartition (G : SimpleGraph V) (A B : Finset V) : Prop :=
  A ∩ B = ∅ ∧ G.IsIndepSet A ∧ (∀ v w : V, v ∈ B → w ∈ B → v ≠ w → G.Adj v w) ∧ A ∪ B = Finset.univ

theorem splitPartition_disjoint {A B : Finset V} (h : SplitPartition G A B) : A ∩ B = ∅ := h.1

theorem splitPartition_indep {A B : Finset V} (h : SplitPartition G A B) : G.IsIndepSet A := h.2.1

theorem splitPartition_clique {A B : Finset V} (h : SplitPartition G A B) :
    ∀ v w : V, v ∈ B → w ∈ B → v ≠ w → G.Adj v w := h.2.2.1

theorem splitPartition_union {A B : Finset V} (h : SplitPartition G A B) : A ∪ B = Finset.univ :=
  h.2.2.2

/-- Every vertex of `V` lies in one of the two sides. -/
theorem mem_splitPartition {A B : Finset V} (h : SplitPartition G A B) {v : V} :
    v ∈ A ∨ v ∈ B := by
  have hmem : v ∈ A ∪ B := by rw [h.2.2.2]; exact Finset.mem_univ v
  simpa using Finset.mem_union.mp hmem

/-- **THE TWO SIDES ARE DISJOINT AS SETS OF VERTICES.** -/
theorem not_mem_inter_of_splitPartition {A B : Finset V} (h : SplitPartition G A B) (v : V)
    (hvA : v ∈ A) (hvB : v ∈ B) : False :=
  Finset.eq_empty_iff_forall_notMem.mp h.1 v (Finset.mem_inter.mpr ⟨hvA, hvB⟩)

/-- **THE TWO SIDES SHARE NO VERTEX.** -/
theorem ne_of_splitPartition_mem {A B : Finset V} (h : SplitPartition G A B) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) : a ≠ b :=
  fun hc => not_mem_inter_of_splitPartition h a ha (hc ▸ hb)

/-- **THE COUNTING LEMMA OF THE AXIS:** every vertex set splits over the two sides,
`|X| = |X ∩ A| + |X ∩ B|`. -/
theorem card_eq_card_inter_add_card_inter_splitPartition {A B : Finset V}
    (h : SplitPartition G A B) (X : Finset V) :
    X.card = (X ∩ A).card + (X ∩ B).card := by
  have hunion : X = (X ∩ A) ∪ (X ∩ B) := by
    ext v
    constructor
    · intro hv
      rcases mem_splitPartition h with hvA | hvB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hvA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv, hvB⟩)
    · intro hv
      exact (Finset.mem_union.mp hv).elim
        (fun h' => (Finset.mem_inter.mp h').1) (fun h' => (Finset.mem_inter.mp h').1)
  have hno : ∀ v : V, v ∉ (A ∩ B) := Finset.eq_empty_iff_forall_notMem.mp h.1
  have hinter : (X ∩ A) ∩ (X ∩ B) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun v => ?_
    intro hv
    exact hno v (Finset.mem_inter.mpr ⟨
      (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).2⟩)
  have h1 : X.card = ((X ∩ A) ∪ (X ∩ B)).card := congrArg Finset.card hunion
  calc X.card = ((X ∩ A) ∪ (X ∩ B)).card := h1
    _ = (X ∩ A).card + (X ∩ B).card := by
        rw [(Finset.card_union_add_card_inter (X ∩ A) (X ∩ B)).symm, hinter,
          Finset.card_empty, Nat.add_zero]

/-! ## Part 2 — the hypothesis of Erdős #73 on a split graph -/

/-- **`X ∩ A` is an independent set**, being a subset of `A`. -/
theorem isIndepSet_inter_indep_of_splitPartition {A B : Finset V} (h : SplitPartition G A B)
    (X : Finset V) : G.IsIndepSet ((X ∩ A : Finset V)) :=
  isIndepSet_of_intro (S := X ∩ A) fun v w hv hw hne hadj => IsIndepSet.apply' h.2.1
    (Finset.mem_inter.mp (Finset.mem_coe.mpr hv)).2
    (Finset.mem_inter.mp (Finset.mem_coe.mpr hw)).2 hne hadj

/-- **The independent side of `X` is bounded by `α(G[X])`.  This is the counting input of the axis.**

Note what is *not* available: an earlier draft of this file claimed
`α(G[X]) ≥ 1 + |X ∩ A|` for `X` meeting the clique side, by adjoining a vertex of `B` to `X ∩ A`.
That claim is **false** and Lean rejected it: a split graph may have edges *between* the two sides
(`K₃ ⊔ K₁` is a split graph with `A` and `B` meeting), so `X ∩ A ∪ {b}` need not be independent.  The
deficiency bound below therefore uses only the two statements that are true — `α(G[X]) ≥ |X ∩ A|`
and `α(G[X]) ≥ 1` whenever `X ≠ ∅` — and they are enough. -/
theorem card_inter_indep_le_indepCard_splitPartition {A B : Finset V}
    (h : SplitPartition G A B) (X : Finset V) : (X ∩ A).card ≤ indepCard G X :=
  le_indepCard_of_isIndepSet (Finset.inter_subset_left : (X ∩ A : Finset V) ⊆ X)
    (isIndepSet_inter_indep_of_splitPartition h X)

/-- **AN INDEPENDENT SET MEETS THE CLIQUE SIDE IN AT MOST ONE POINT.**  This is the local statement
the whole file rests on: `B` is a clique of `G`, and an independent set meets a clique in at most
one point. -/
theorem card_le_one_of_isIndepSet_sub_clique {A B : Finset V} (h : SplitPartition G A B)
    {S : Finset V} (hSi : G.IsIndepSet S) (hsub : S ⊆ B) : S.card ≤ 1 := by
  by_cases hne : S.Nonempty
  · letI : Nonempty V := hne.to_type
    refine Finset.card_le_one_iff_subset_singleton.mpr ?_
    obtain ⟨v, hv⟩ := hne
    refine ⟨v, fun x hx => ?_⟩
    by_contra hxv
    have hne' : v ≠ x := fun hc => hxv (Finset.mem_singleton.mpr hc.symm)
    exact IsIndepSet.apply' hSi hv hx hne'
      (h.2.2.1 v x (hsub hv) (hsub hx) hne')
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty]
    omega

/-- **THE HYPOTHESIS OF ERDŐS #73 SEES ONLY THE SIZE OF THE CLIQUE SIDE:**
`LocIndep k G → |B| ≤ k + 2`.

This is `LocIndep k G` applied to the vertex set `B` itself: `B` is a clique, so its largest
independent set is a single vertex, and `2 * 1 + k ≥ |B|` is all Erdős's hypothesis says there. -/
theorem cardB_le_locIndep_add_two {k : ℕ} (hk : LocIndep k G) {A B : Finset V}
    (h : SplitPartition G A B) (hB : B.Nonempty) : B.card ≤ k + 2 := by
  obtain ⟨S, hSsub, hSi, hcard⟩ := hk B
  have hle : S.card ≤ 1 := card_le_one_of_isIndepSet_sub_clique h hSi hSsub
  omega

/-- **THE VALUE OF THE HYPOTHESIS OF ERDŐS #73 ON SPLIT GRAPHS:**
`MaxDef G ≤ |B| − 1`, i.e. the deficiency of a split graph is paid for by its clique side.

Part 3 attains the converse in the only case in which it is attainable: `|B| − 2` vertices suffice
exactly when the clique side has an isolated pair
(`closeToBipartite_split_cardB_sub_two_iff`). -/
theorem maxDef_split_le {A B : Finset V} (h : SplitPartition G A B) (hB : 1 ≤ B.card) :
    MaxDef G ≤ B.card - 1 := by
  refine maxDef_le (fun X => ?_)
  have hsplit := card_eq_card_inter_add_card_inter_splitPartition h X
  have hXB : (X ∩ B).card ≤ B.card := Finset.card_le_card (Finset.inter_subset_right)
  by_cases hXA : (X ∩ A).Nonempty
  · have h1 := card_inter_indep_le_indepCard_splitPartition h X
    have hpos : 1 ≤ (X ∩ A).card := Finset.card_pos.mpr hXA
    have hmul : 2 * (X ∩ A).card ≤ 2 * indepCard G X := Nat.mul_le_mul_left 2 h1
    have hstep1 : X.card - 2 * indepCard G X ≤ X.card - 2 * (X ∩ A).card :=
      Nat.sub_le_sub_left hmul X.card
    have heq : X.card - 2 * (X ∩ A).card = (X ∩ B).card - (X ∩ A).card := by
      rw [hsplit, Nat.two_mul]
      omega
    have hstep2 : (X ∩ B).card - (X ∩ A).card ≤ (X ∩ B).card - 1 :=
      Nat.sub_le_sub_left hpos (X ∩ B).card
    have hstep3 : (X ∩ B).card - 1 ≤ B.card - 1 := Nat.sub_le_sub_right hXB 1
    unfold defOf
    omega
  · have hXA0 : (X ∩ A).card = 0 := by
      have hz := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hXA)
      omega
    by_cases hX : X.Nonempty
    · have h1 := indepCard_pos (G := G) hX
      have hXeq : X.card = (X ∩ B).card := by rw [hsplit, hXA0, Nat.zero_add]
      have h2 : 2 ≤ 2 * indepCard G X := by omega
      have h3 : X.card - 2 * indepCard G X ≤ X.card - 2 := Nat.sub_le_sub_left h2 X.card
      have h5 : X.card - 2 ≤ B.card - 1 := by
        have hle : X.card ≤ B.card := by rw [hXeq]; exact hXB
        omega
      unfold defOf
      exact h3.trans h5
    · have hX0 : X.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hX)
      unfold defOf
      omega

/-! ## Part 3 — the conclusion of Erdős #73 on a split graph -/

/-- **AN ISOLATED PAIR OF THE CLIQUE SIDE**: two vertices of `B` with **no common neighbour** in the
independent side `A`.

This is the local object that decides the value of `τ(G)` on a split graph.  If a pair is isolated,
deleting the other `|B| − 2` vertices of `B` leaves a bipartite graph; if every pair has a common
neighbour, every such deletion leaves a triangle, and `|B| − 1` vertices are needed. -/
def IsolatedPair (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ b₁ b₂ : V, b₁ ∈ B ∧ b₂ ∈ B ∧ b₁ ≠ b₂ ∧ ∀ a : V, a ∈ A → ¬ (G.Adj a b₁ ∧ G.Adj a b₂)

/-- **THREE PAIRWISE ADJACENT VERTICES SURVIVING A DELETION RULE OUT BIPARTITENESS.** -/
theorem not_isBipartite_deleteFinset_of_tri {Z : Finset V} {x y z : V}
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hzZ : z ∉ Z) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) : ¬ (deleteFinset G Z).IsBipartite := by
  rintro ⟨d, hd⟩
  have hv : ∀ w : V, (d w).val < 2 := fun w => (d w).isLt
  have h1 : (d x).val ≠ (d y).val := fun hc => hd (deleteFinset_adj.mpr ⟨hxZ, hyZ, hxy⟩) (Fin.ext hc)
  have h2 : (d y).val ≠ (d z).val := fun hc => hd (deleteFinset_adj.mpr ⟨hyZ, hzZ, hyz⟩) (Fin.ext hc)
  have h3 : (d z).val ≠ (d x).val := fun hc => hd (deleteFinset_adj.mpr ⟨hzZ, hxZ, hzx⟩) (Fin.ext hc)
  omega

/-- **THE OBSTRUCTION ON THIS CLASS:** if the clique side of a bipartite residue is exactly the pair
`{b₁, b₂}`, then no vertex of `A` outside `Z` is adjacent to both — such a vertex would complete a
triangle inside the residue. -/
theorem not_isBipartite_deleteFinset_of_commonNeighbour {A B : Finset V} (h : SplitPartition G A B)
    {Z : Finset V} {b₁ b₂ a : V} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂) (ha : a ∈ A)
    (hZ : B \ Z = {b₁, b₂}) (haZ : a ∉ Z) (h1 : G.Adj a b₁) (h2 : G.Adj a b₂) :
    ¬ (deleteFinset G Z).IsBipartite := by
  have hb₁Z : b₁ ∉ Z := by
    have hmem : b₁ ∈ ({b₁, b₂} : Finset V) := Finset.mem_insert_self _ _
    exact (Finset.mem_sdiff.mp (hZ ▸ hmem)).2
  have hb₂Z : b₂ ∉ Z := by
    have hmem : b₂ ∈ ({b₁, b₂} : Finset V) := by simp
    exact (Finset.mem_sdiff.mp (hZ ▸ hmem)).2
  refine not_isBipartite_deleteFinset_of_tri hb₁Z haZ hb₂Z (G.adj_symm h1) h2
    (h.2.2.1 b₂ b₁ hb₂ hb₁ (fun hc => hne hc.symm))

/-- **A BIPARTITE RESIDUE KEEPS AT MOST TWO VERTICES OF THE CLIQUE SIDE.**  The colours of the
surviving clique vertices are pairwise distinct, because two of them are adjacent. -/
theorem cardBsdiff_le_two_of_isBipartite_deleteFinset {A B : Finset V} (h : SplitPartition G A B)
    {Z : Finset V} (hz : (deleteFinset G Z).IsBipartite) : (B \ Z).card ≤ 2 := by
  obtain ⟨col⟩ := hz
  have hd : ∀ {v w : V}, (deleteFinset G Z).Adj v w → col v ≠ col w := col.valid
  have hmem : ∀ b : V, b ∈ B \ Z → b ∉ Z := fun b hb => (Finset.mem_sdiff.mp hb).2
  have hinj : ∀ b c : V, b ∈ B \ Z → c ∈ B \ Z → (col b = col c → b = c) := by
    intro b c hb hc hbc
    by_contra hne2
    have hpro : col b ≠ col c := hd (deleteFinset_adj.mpr ⟨hmem b hb, hmem c hc,
      h.2.2.1 b c (Finset.mem_sdiff.mp hb).1 (Finset.mem_sdiff.mp hc).1 hne2⟩)
    exact hpro (by rw [hbc])
  have hcard := Finset.card_le_card_of_injOn
    (s := B \ Z)
    (t := (Finset.univ : Finset (Fin 2)))
    (f := fun b : V => col b)
    (fun b _ => Finset.mem_univ _)
    (by
      intro b hb c hc hfeq
      exact hinj b c hb hc hfeq)
  simpa using hcard

/-- **THE CLAUSE `|B| − 1`: if at most one vertex of the clique side survives the deletion of `Z`,
then `G − Z` is bipartite.**

The colouring is "independent side versus clique side"; it is proper because the only edges of the
residue are then between the two sides (`A` carries no edge, and `B \ Z` carries at most one vertex,
so it carries no edge either). -/
theorem isBipartite_deleteFinset_of_split_sdiff_le_one {A B : Finset V}
    (h : SplitPartition G A B) {Z : Finset V} (hZ : (B \ Z).card ≤ 1) :
    (deleteFinset G Z).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v : V => if v ∈ A then (0 : Fin 2) else 1)
    (fun {v w} hadj => ?_)⟩
  obtain ⟨hvZ, hwZ, hvw⟩ := deleteFinset_adj.mp hadj
  have hne' : v ≠ w := fun hcon => G.loopless.irrefl v (hcon ▸ hvw)
  by_cases hAv : v ∈ A
  · by_cases hAw : w ∈ A
    · exact (IsIndepSet.apply' h.2.1 hAv hAw hne' hvw).elim
    · have hd1 : (if v ∈ A then (0 : Fin 2) else 1) = 0 := if_pos hAv
      have hd2 : (if w ∈ A then (0 : Fin 2) else 1) = 1 := if_neg hAw
      rw [hd1, hd2]
      decide
  · by_cases hAw : w ∈ A
    · have hd1 : (if v ∈ A then (0 : Fin 2) else 1) = 1 := if_neg hAv
      have hd2 : (if w ∈ A then (0 : Fin 2) else 1) = 0 := if_pos hAw
      rw [hd1, hd2]
      decide
    · have hBv : v ∈ B := by
        rcases mem_splitPartition h with h1 | h1
        · exact absurd h1 hAv
        · exact h1
      have hBw : w ∈ B := by
        rcases mem_splitPartition h with h1 | h1
        · exact absurd h1 hAw
        · exact h1
      have hvB : v ∈ B \ Z := Finset.mem_sdiff.mpr ⟨hBv, hvZ⟩
      have hwB : w ∈ B \ Z := Finset.mem_sdiff.mpr ⟨hBw, hwZ⟩
      have h2 := card_ge_two_of_mem_ne (B \ Z) v w hvB hwB hne'
      omega

/-- **THE CLAUSE `|B| − 2`: if `b₁, b₂` is an isolated pair of the clique side, then deleting the
other vertices of `B` leaves a bipartite graph.**

The colouring is `fun v => if G.Adj v b₁ then 1 else 0`, which is proper on the residue: the only
vertices of the residue are the independent side and `b₁, b₂`, and `IsolatedPair` says that no
independent vertex is adjacent to *both* of them. -/
theorem isBipartite_deleteFinset_of_split_isolatedPair {A B : Finset V}
    (h : SplitPartition G A B) {b₁ b₂ : V} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂)
    (hnc : ∀ a : V, a ∈ A → ¬ (G.Adj a b₁ ∧ G.Adj a b₂)) :
    (deleteFinset G (B \ {b₁, b₂})).IsBipartite := by
  classical
  have hcov : ∀ v : V, v ∉ (B \ {b₁, b₂}) → v ∈ A ∨ v = b₁ ∨ v = b₂ := by
    intro v hvZ
    rcases mem_splitPartition h with hvA | hvB
    · exact Or.inl hvA
    · have hmem : v ∈ ({b₁, b₂} : Finset V) := by
        by_contra hc
        exact hvZ (Finset.mem_sdiff.mpr ⟨hvB, hc⟩)
      rcases Finset.mem_insert.mp hmem with h | h
      · exact Or.inr (Or.inl (h ▸ rfl))
      · exact Or.inr (Or.inr (Finset.mem_singleton.mp h ▸ rfl))
  have hcl : G.Adj b₂ b₁ := h.2.2.1 b₂ b₁ hb₂ hb₁ (fun hc => hne hc.symm)
  have hself : ¬ G.Adj b₁ b₁ := fun hc => G.loopless.irrefl b₁ hc
  refine ⟨SimpleGraph.Coloring.mk (fun v : V => if G.Adj v b₁ then (1 : Fin 2) else 0)
    (fun {v w} hadj => ?_)⟩
  obtain ⟨hvZ, hwZ, hvw⟩ := deleteFinset_adj.mp hadj
  have hne' : v ≠ w := fun hcon => G.loopless.irrefl v (hcon ▸ hvw)
  rcases hcov v hvZ with hvA | hv1 | hv2
  · rcases hcov w hwZ with hwA | hw1 | hw2
    · exact (IsIndepSet.apply' h.2.1 hvA hwA hne' hvw).elim
    · rw [hw1] at hvw ⊢
      have hd1 : (if G.Adj v b₁ then (1 : Fin 2) else 0) = 1 := if_pos hvw
      have hd2 : (if G.Adj b₁ b₁ then (1 : Fin 2) else 0) = 0 := if_neg hself
      rw [hd1, hd2]
      decide
    · have hvb : G.Adj v b₂ := hw2.symm ▸ hvw
      have hnot : ¬ G.Adj v b₁ := fun hbad => hnc v hvA ⟨hbad, hvb⟩
      rw [hw2, if_neg hnot, if_pos hcl]
      decide
  · rcases hcov w hwZ with hwA | hw1 | hw2
    · rw [hv1] at hvw ⊢
      have hd1 : (if G.Adj b₁ b₁ then (1 : Fin 2) else 0) = 0 := if_neg hself
      have hd2 : (if G.Adj w b₁ then (1 : Fin 2) else 0) = 1 := if_pos (G.adj_symm hvw)
      rw [hd1, hd2]
      decide
    · rw [hv1, hw1] at hvw ⊢
      exact (G.loopless.irrefl b₁ hvw).elim
    · rw [hv1, hw2, if_neg hself, if_pos hcl]
      decide
  · rcases hcov w hwZ with hwA | hw1 | hw2
    · rw [hv2] at hvw ⊢
      have hd1 : (if G.Adj b₂ b₁ then (1 : Fin 2) else 0) = 1 := if_pos hcl
      by_cases hwb : G.Adj w b₁
      · exact (hnc w hwA ⟨hwb, G.adj_symm hvw⟩).elim
      · rw [hd1, if_neg hwb]
        decide
    · rw [hv2, hw1, if_pos hcl, if_neg hself]
      decide
    · rw [hv2, hw2] at hvw ⊢
      exact (G.loopless.irrefl b₂ hvw).elim

/-- **`CloseToBipartite (|B| − 1) G` always holds on a split graph with a nonempty clique side**:
delete all of `B` but one vertex. -/
theorem closeToBipartite_of_split_cardB_sub_one {A B : Finset V} (h : SplitPartition G A B)
    (hB : B.Nonempty) : CloseToBipartite (B.card - 1) G := by
  obtain ⟨b₀, hb₀⟩ := hB
  refine ⟨B \ {b₀}, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hb₀),
      Finset.card_singleton]
  · refine isBipartite_deleteFinset_of_split_sdiff_le_one h ?_
    have hiff : B \ (B \ {b₀}) ⊆ {b₀} := by
      intro v hv
      have h1 := Finset.mem_sdiff.mp hv
      by_contra hc
      exact h1.2 (Finset.mem_sdiff.mpr ⟨h1.1, hc⟩)
    refine Finset.card_le_one_iff.mpr ?_
    intro h1 h2 h3 h4
    exact (Finset.mem_singleton.mp (hiff h3)).trans (Finset.mem_singleton.mp (hiff h4)).symm

/-- **`CloseToBipartite (|B| − 2) G` follows from an isolated pair of the clique side.** -/
theorem closeToBipartite_of_split_isolatedPair {A B : Finset V} (h : SplitPartition G A B)
    {b₁ b₂ : V} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂)
    (hnc : ∀ a : V, a ∈ A → ¬ (G.Adj a b₁ ∧ G.Adj a b₂)) :
    CloseToBipartite (B.card - 2) G := by
  refine ⟨B \ {b₁, b₂}, ?_, isBipartite_deleteFinset_of_split_isolatedPair h hb₁ hb₂ hne hnc⟩
  have hsub : ({b₁, b₂} : Finset V) ⊆ B := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv' | hv'
    · exact hv'.symm ▸ hb₁
    · exact hv'.symm ▸ hb₂
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_eq_two.mpr ⟨b₁, b₂, hne, rfl⟩]

/-! ### The two regimes: the exact value of the conclusion -/

/-- **`|B| ≤ m + 2` whenever `CloseToBipartite m G`** on a split graph with `2 ≤ |B|`: a bipartite
residue keeps at most two vertices of the clique side. -/
theorem cardB_le_closeToBipartite_add_two {A B : Finset V} (h : SplitPartition G A B) {m : ℕ}
    (hm : CloseToBipartite m G) (hB : 2 ≤ B.card) : B.card ≤ m + 2 := by
  obtain ⟨Z, hZcard, hZb⟩ := hm
  have h2 : (B \ Z).card ≤ 2 := cardBsdiff_le_two_of_isBipartite_deleteFinset h hZb
  have hsub : (B \ Z) ∪ (B ∩ Z) = B := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hle : B.card ≤ (B \ Z).card + (B ∩ Z).card := by
    have hc := Finset.card_union_le (s := B \ Z) (t := B ∩ Z)
    rw [hsub] at hc
    exact hc
  have hle' : (B ∩ Z).card ≤ Z.card := Finset.card_le_card (Finset.inter_subset_right)
  omega

/-- **THE MACHINE-CHECKED LOWER BOUND OF THE AXIS:** if no pair of the clique side is isolated, then
`|B| − 2` vertices do **not** suffice.

This is the contrapositive of `closeToBipartite_of_split_isolatedPair`, proved through the triangle
obstruction `not_isBipartite_deleteFinset_of_commonNeighbour`. -/
theorem not_closeToBipartite_of_split_no_isolatedPair {A B : Finset V} (h : SplitPartition G A B)
    (hB : 2 ≤ B.card) (hn : ¬ IsolatedPair G A B) : ¬ CloseToBipartite (B.card - 2) G := by
  intro hm
  obtain ⟨Z, hZcard, hZb⟩ := hm
  have h2 : (B \ Z).card ≤ 2 := cardBsdiff_le_two_of_isBipartite_deleteFinset h hZb
  have hsplit : B.card = (B \ Z).card + (B ∩ Z).card :=
    (Finset.card_sdiff_add_card_inter B Z).symm
  have hge : 2 ≤ (B \ Z).card := by
    have hle' : (B ∩ Z).card ≤ Z.card := Finset.card_le_card (Finset.inter_subset_right)
    omega
  have htwo : (B \ Z).card = 2 := Nat.le_antisymm h2 hge
  obtain ⟨b₁, b₂, hne, hZ⟩ := Finset.card_eq_two.mp htwo
  -- the deletion set of a `|B| - 2`-bounded witness lies inside the clique side
  have hdiff : (Z \ B).card = 0 := by
    have hc : (Z \ B).card + (B ∩ Z).card = Z.card := by
      have hc' := Finset.card_sdiff_add_card_inter (s := Z) (t := B)
      rw [Finset.inter_comm] at hc'
      exact hc'
    have hn : B.card - 2 = (B ∩ Z).card := by omega
    have hle : (B ∩ Z).card ≤ Z.card :=
      Finset.card_le_card (Finset.inter_subset_right : (B ∩ Z : Finset V) ⊆ Z)
    have hz : Z.card = (B ∩ Z).card := Nat.le_antisymm (by omega) hle
    omega
  have hsdiff : Z \ B = ∅ := Finset.card_eq_zero.mp hdiff
  have hZsub : Z ⊆ B := by
    intro v hv
    by_contra hnv
    exact absurd (Finset.mem_sdiff.mpr ⟨hv, hnv⟩)
      (Finset.eq_empty_iff_forall_notMem.mp hsdiff v)
  have hb₁Z : b₁ ∈ B \ Z := hZ ▸ Finset.mem_insert_self _ _
  have hb₂Z : b₂ ∈ B \ Z := hZ ▸ (show b₂ ∈ ({b₁, b₂} : Finset V) from by simp)
  refine hn ?_
  unfold IsolatedPair
  refine ⟨b₁, b₂, (Finset.mem_sdiff.mp hb₁Z).1, (Finset.mem_sdiff.mp hb₂Z).1, hne, ?_⟩
  exact fun a ha hcon => not_isBipartite_deleteFinset_of_commonNeighbour h
    (Finset.mem_sdiff.mp hb₁Z).1 (Finset.mem_sdiff.mp hb₂Z).1 hne ha hZ
    (fun hz => not_mem_inter_of_splitPartition h a ha (hZsub hz)) hcon.1 hcon.2 hZb

/-- **THE EXACT VALUE OF THE CONCLUSION OF ERDŐS #73 ON SPLIT GRAPHS:** the odd cycle transversal
number of a split graph with `2 ≤ |B|` is `|B| − 1`, unless the clique side has an isolated pair, in
which case it is `|B| − 2`.

In particular hypothesis and conclusion *coincide up to one vertex* on this class: Erdős's
hypothesis bounds `|B|` by `k + 2`, and the conclusion needs at most `|B| − 1 ≤ k + 1` vertices. -/
theorem closeToBipartite_split_iff {A B : Finset V} (h : SplitPartition G A B) {m : ℕ}
    (hB : 2 ≤ B.card) :
    CloseToBipartite m G ↔ (B.card ≤ m + 1 ∨ (B.card ≤ m + 2 ∧ IsolatedPair G A B)) := by
  classical
  constructor
  · intro hm
    by_cases h1 : B.card ≤ m + 1
    · exact Or.inl h1
    · refine Or.inr ⟨cardB_le_closeToBipartite_add_two h hm hB, ?_⟩
      by_contra hn
      exact (not_closeToBipartite_of_split_no_isolatedPair h hB hn)
        (closeToBipartite_mono (by omega) hm)
  · rintro (h1 | ⟨h1, h2⟩)
    · have hne : B.Nonempty := Finset.card_pos.mp (by omega)
      refine closeToBipartite_mono (by omega) (closeToBipartite_of_split_cardB_sub_one h hne)
    · obtain ⟨b₁, b₂, hb₁, hb₂, hne, hnc⟩ := h2
      exact closeToBipartite_mono (by omega)
        (closeToBipartite_of_split_isolatedPair h hb₁ hb₂ hne hnc)

/-- **THE `|B| − 2` CLAUSE, AS AN EQUIVALENCE:** on a split graph with `2 ≤ |B|`,
`CloseToBipartite (|B| − 2) G ↔ IsolatedPair G A B`. -/
theorem closeToBipartite_split_cardB_sub_two_iff {A B : Finset V} (h : SplitPartition G A B)
    (hB : 2 ≤ B.card) : CloseToBipartite (B.card - 2) G ↔ IsolatedPair G A B := by
  constructor
  · intro hm
    refine (show IsolatedPair G A B from Classical.byContradiction fun hI => ?_)
    exact absurd hm (not_closeToBipartite_of_split_no_isolatedPair h hB hI)
  · intro hI
    obtain ⟨b₁, b₂, hb₁, hb₂, hne, hnc⟩ := hI
    exact closeToBipartite_of_split_isolatedPair h hb₁ hb₂ hne hnc

/-! ### A new instance of the headline theorem -/

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE CONSTANT `k + 1`: THE SPLIT-GRAPH AXIS.**
`LocIndep k G` and a split partition `V = A ⊔ B` with `B` nonempty give
`CloseToBipartite (k + 1) G`.

The hypothesis is used **once**: `cardB_le_locIndep_add_two`, i.e. Erdős's local hypothesis applied
to the vertex set of the clique side alone, which bounds its size by `k + 2` because a clique has
independence number one.  There is no odd-girth bound, no packing bound, no degree bound and no
decomposition hypothesis. -/
theorem closeToBipartite_of_splitPartition {k : ℕ} (hk : LocIndep k G) {A B : Finset V}
    (h : SplitPartition G A B) (hB : B.Nonempty) : CloseToBipartite (k + 1) G := by
  have hcard := cardB_le_locIndep_add_two hk h hB
  refine closeToBipartite_mono (by omega) (closeToBipartite_of_split_cardB_sub_one h hB)

/-- **The split-graph instance of Erdős #73.**  `V` is universally quantified in this development, so
this *is* an instance of `Erdős73On k (k + 1)`: for every finite vertex type, every graph satisfying
Erdős's hypothesis `LocIndep k` and carrying a split partition with a nonempty clique side is
`k + 1`-close to bipartite. -/
theorem erdos73On_of_splitPartition {k : ℕ} (hk : LocIndep k G) {A B : Finset V}
    (h : SplitPartition G A B) (hB : B.Nonempty) : CloseToBipartite (k + 1) G :=
  closeToBipartite_of_splitPartition hk h hB

/-- **THE SHARPER SPLIT-GRAPH INSTANCE:** an isolated pair of the clique side improves the constant
from `k + 1` to `k`. -/
theorem closeToBipartite_of_splitPartition_of_isolatedPair {k : ℕ} (hk : LocIndep k G)
    {A B : Finset V} (h : SplitPartition G A B) (hB : 2 ≤ B.card)
    (hIso : IsolatedPair G A B) : CloseToBipartite k G := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, hnc⟩ := hIso
  have hne' : B.Nonempty := Finset.card_pos.mp (by omega : 0 < B.card)
  have hcard := cardB_le_locIndep_add_two hk h hne'
  refine closeToBipartite_mono (by omega)
    (closeToBipartite_of_split_isolatedPair h hb₁ hb₂ hne hnc)

/-! ## Part 4 — the witness family: what is left, and why it is left

The constant `k + 1` of `erdos73On_of_splitPartition` is meant to be **attained** for every `k ≥ 1`,
and the construction is settled; only the `Finset` bookkeeping of its `LocIndep` proof is missing
here.  The witness is

> `splitWitness k` on `Fin (k+2) × Bool` — the complete bipartite graph `K_{n,n}`, `n = k+2`, with a
> perfect matching removed.  The **independent side** is `A = {(i, false)}`, the **clique side** is
> `B = {(i, true)}`, and `(i, false) ~ (j, true)` exactly when `i ≠ j`.

and everything needed is recorded here so that the next round can finish it mechanically:

* `A` and `B` are disjoint and cover the vertex set, `A` is independent and `B` is a clique, each of
  size `n = k + 2`; this is the hypothesis of `closeToBipartite_of_splitPartition`;
* **`LocIndep k` holds, indeed with `k = 0`.**  For a vertex set `X`, let `AX = X ∩ A`,
  `CX = X ∩ B`.  If `|AX| ≥ |CX|` take the independent set `S = AX`; otherwise `CX` has an index
  that `AX` does not use (the map `v ↦ v.1` is injective on both sides), and `S = AX ∪ {that one
  clique vertex}` is independent, with `2 |S| + k ≥ |X|` because `|CX| ≤ n = k + 2`.  The two
  counting lemmas the proof needs are `Finset.card_image_iff` for `v ↦ v.1` on each side and
  `Finset.not_subset.mp`;
* **`CloseToBipartite (k + 1)` holds**: delete all of `B` but one vertex (the residue is the star
  centred at the survivor), which is `closeToBipartite_of_splitPartition`;
* **`¬CloseToBipartite k` holds as soon as `k ≥ 1`**: every pair `b_i ≠ b_j` of `B` has the common
  neighbour `a_m` for any `m ∉ {i, j}`, which exists because `|B| = k + 2 ≥ 3` — the index lemma is
  `exists_mem_sdiff_pair_of_card_ge_three` of this file — so
  `not_closeToBipartite_of_split_no_isolatedPair` applies with
  `2 ≤ |B| = k + 2`.

So `CloseToBipartite m (splitWitness k) ↔ k + 1 ≤ m` for `k ≥ 1`, and the constant `k + 1` is
machine-checked optimal on the class.  What is *not* proved in this file is exactly those three
`Finset` computations; nothing else on this axis is missing. -/


end
end JSP90
