/-
# JSP-000090 — `JSPProblem/Multi.lean`: the COMPLETE MULTIPARTITE axis (round 106)

The header of this file, the twenty-ninth family of attacks on Erdős Problem #73, is worth reading
before the Lean.

## What this file adds

`JSPProblem/Exact.lean` (round 105) proved that both sides of Erdős #73 are **exactly additive over
an anticomplete cover** of the vertex set, and recorded its own limit: an anticomplete cover of `V`
with two nonempty pieces *is* a disconnection, so the additive axis only pays for **disconnected**
graphs.  The graphs that the additive axis cannot reach are the connected ones, and among those the
most elementary family is the **complete multipartite graph** `K_{n,…,n}` — the join of `t`
independent sets of size `n`.

For a complete multipartite graph all three quantities that are only *comparable* in general are
equal, and their common value can be written down:

| quantity | value on `multi t n` |
| --- | --- |
| `α(G[X])`, any `X ⊆ V` | a number in `{0, …, n}` (an independent set lies in one part) |
| `MaxDef G`, the hypothesis of Erdős #73 | `(t − 2) * n` |
| `τ(G)`, the conclusion of Erdős #73 | `(t − 2) * n` |

so on this class the hypothesis and the conclusion of Erdős #73 **coincide**, and the theorem holds
with the **optimal constant `f(k) = k`** — the same constant as round 98's disjoint-odd-cycles
class, round 100's maximum-degree-`≤ 2` class, round 104's cluster graphs and round 105's cover
closure of them, but on a **different** class: `multi t n` is **connected** whenever `2 ≤ t`, so no
anticomplete-decomposition instance applies to it, and for `n ≥ 2` it is not a cluster graph
(`K_{2,2,2}` has no clique of size `3`); `isBipartite_multi_of_le_two` records that the family
leaves the bipartite world as soon as there are three parts.

## The declarations

```
JSP90.multi                          the complete multipartite graph with t parts of n vertices
JSP90.multiPart                      its i-th part
JSP90.card_eq_sum_card_multiPart     |X| = ∑ i, |X ∩ P_i|   (the counting lemma of the file)
JSP90.indepCard_le_multi             α(G[X]) ≤ n
JSP90.card_le_mul_indepCard_multi    |X| ≤ t * α(G[X])       (so X is (t-2)*α-deficient)
JSP90.maxDef_multi                   MaxDef (multi t n) = (t - 2) * n
JSP90.locIndep_multi_iff             LocIndep k (multi t n) ↔ (t - 2) * n ≤ k
JSP90.isBipartite_deleteFinset_multi_iff
                                    G − X is bipartite  ↔  its vertices lie in at most two parts
JSP90.closeToBipartite_iff_multi     CloseToBipartite m (multi t n) ↔ (t - 2) * n ≤ m
JSP90.erdos73On_of_multi             A NEW INSTANCE OF THE HEADLINE THEOREM, constant k
JSP90.erdos73On_of_multi_optimal     ... and its optimality, machine-checked
```

## What is *not* proved

`jsp_000090_main` is not declared and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas)
is unchanged: this file is about a class, not about the general case.  What it adds to the
*reduction* is one more piece of evidence about the shape of the missing theorem — the identity
function `f(k) = k` is now proved on five structurally unrelated classes, none of which contains a
3-connected graph of large odd girth, so the obstruction really is the 3-connected case and not the
accounting.
-/
import JSPProblem.Deficiency
import JSPProblem.Additive
import JSPProblem.Cluster

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type u} [Fintype V]

noncomputable section

/-! ## Part 1 — the graph and its parts -/

section Multi

variable {t n : ℕ}

/-- **The complete multipartite graph with `t` parts of `n` vertices each**, on the vertex type
`Fin t × Fin n`: vertex `(i, j)` is the `j`-th vertex of the `i`-th part, and two vertices are
adjacent exactly when they lie in different parts. -/
def multi (t n : ℕ) : SimpleGraph (Fin t × Fin n) where
  Adj p q := p.1 ≠ q.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun p h => h rfl⟩

@[simp] theorem multi_adj {p q : Fin t × Fin n} :
    (multi t n).Adj p q ↔ p.1 ≠ q.1 := Iff.rfl

/-- **The `i`-th part of `multi t n`**: the `n` vertices `(i, j)`, `j < n`.  Independent sets of a
complete multipartite graph are exactly the sets inside one part, so this is the object all the
counting lemmas below are about. -/
def multiPart (t n : ℕ) (i : Fin t) : Finset (Fin t × Fin n) :=
  (Finset.univ : Finset (Fin n)).image (fun j => (i, j))

@[simp] theorem mem_multiPart {i : Fin t} {p : Fin t × Fin n} :
    p ∈ multiPart t n i ↔ ∃ j : Fin n, p = (i, j) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, _, hj⟩
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **Membership in a part only depends on the part index.** -/
theorem mem_multiPart_iff {i : Fin t} {p : Fin t × Fin n} :
    p ∈ multiPart t n i ↔ p.1 = i := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_multiPart.mp h
    simp only [Prod.fst, hj]
  · intro h
    exact mem_multiPart.mpr ⟨p.2, Prod.ext h rfl⟩

theorem card_multiPart (i : Fin t) : (multiPart t n i).card = n := by
  have hinj : Function.Injective (fun j : Fin n => (i, j)) :=
    fun a b hab => (Prod.mk.inj hab).2
  have h := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hinj
  simpa [multiPart] using h

/-- Two different parts are disjoint. -/
theorem multiPart_disjoint {i j : Fin t} (h : i ≠ j) :
    Disjoint (multiPart t n i) (multiPart t n j) := by
  refine Finset.disjoint_left.2 fun p hp hq => ?_
  have h1 : i = p.1 := (mem_multiPart_iff.mp hp).symm
  have h2 : p.1 = j := mem_multiPart_iff.mp hq
  exact h (h1.trans h2)

/-- **A part is an independent set.** -/
theorem isIndepSet_multiPart (i : Fin t) : (multi t n).IsIndepSet (multiPart t n i) := by
  refine isIndepSet_of_intro fun p q hp hq hne hadj => ?_
  have hp' : p ∈ multiPart t n i := Finset.mem_coe.mpr hp
  have hq' : q ∈ multiPart t n i := Finset.mem_coe.mpr hq
  rw [mem_multiPart_iff] at hp' hq'
  exact hadj (hp'.trans hq'.symm)

/-- **A vertex set of `multi t n` splits over the parts**: `|X| = ∑ i, |X ∩ P_i|`.  This is the
counting lemma of the file.  The parts partition the vertex set, but Mathlib's disjoint-union
formula `Finset.card_biUnion` (which in this revision does not apply to a finset of finsets, see
`JSPProblem/Cluster.lean`) cannot be used in this orientation, so the identity is proved by
induction on `X`. -/
theorem card_eq_sum_card_multiPart (X : Finset (Fin t × Fin n)) :
    X.card = ∑ i : Fin t, (X ∩ multiPart t n i).card := by
  induction X using Finset.induction_on with
  | empty => simp
  | @insert p X hX ih =>
      have key : ∀ i : Fin t, (insert p X ∩ multiPart t n i).card
          = (X ∩ multiPart t n i).card + (if p ∈ multiPart t n i then 1 else 0) := by
        intro i
        by_cases hpi : p ∈ multiPart t n i
        · have hnot : p ∉ X ∩ multiPart t n i := fun h => hX (Finset.mem_inter.mp h).1
          rw [Finset.insert_inter_of_mem hpi, Finset.card_insert_of_notMem hnot, if_pos hpi]
        · rw [Finset.insert_inter_of_notMem hpi, if_neg hpi, Nat.add_zero]
      have hone : ∑ i : Fin t, (if p ∈ multiPart t n i then 1 else 0) = 1 := by
        have hkey : ∀ i : Fin t, (if p ∈ multiPart t n i then 1 else 0)
            = if p.1 = i then 1 else 0 := by
          intro i
          by_cases h : p.1 = i
          · have hp : p ∈ multiPart t n i := mem_multiPart_iff.mpr h
            simp [hp, h]
          · have hp : p ∉ multiPart t n i := fun hh => h (mem_multiPart_iff.mp hh)
            simp [hp, h]
        rw [Finset.sum_congr rfl (fun i _ => hkey i)]
        have hh := Finset.sum_ite_eq (Finset.univ : Finset (Fin t)) p.1 (fun _ => 1)
        simpa only [Finset.mem_univ, if_true] using hh
      have hsum : (∑ i : Fin t, (insert p X ∩ multiPart t n i).card)
          = ∑ i : Fin t, (X ∩ multiPart t n i).card + 1 := by
        rw [Finset.sum_congr rfl (fun i _ => key i)]
        rw [Finset.sum_add_distrib, hone]
      rw [Finset.card_insert_of_notMem hX, hsum, ih]

/-! ### The independence number of an induced subgraph -/

/-- **An independent set of `multi t n` lies in a single part.**  Two vertices in different parts
are adjacent, so an independent set cannot meet two parts. -/
theorem subset_multiPart_of_isIndepSet {S : Finset (Fin t × Fin n)} (h : (multi t n).IsIndepSet S)
    (hne : S.Nonempty) : ∃ i : Fin t, S ⊆ multiPart t n i := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p.1, ?_⟩
  intro q hq
  by_cases hqp : q = p
  · subst hqp
    exact mem_multiPart.mpr ⟨q.2, Prod.mk.eta⟩
  · have hnq : ¬ (multi t n).Adj p q := IsIndepSet.apply' h hp hq (Ne.symm hqp)
    have hpq : (multi t n).Adj p q ↔ p.1 ≠ q.1 := multi_adj
    have h1 : p.1 = q.1 := by
      by_contra hc
      exact hnq (hpq.mpr hc)
    exact mem_multiPart.mpr ⟨q.2, Prod.ext h1.symm rfl⟩

/-- **The independence number of an induced subgraph of `multi t n` is at most `n`**, because an
independent set is contained in a part and every part has `n` vertices. -/
theorem indepCard_le_multi (X : Finset (Fin t × Fin n)) : indepCard (multi t n) X ≤ n := by
  obtain ⟨S, hSsub, hSi, hcard⟩ := exists_indepCard (multi t n) X
  by_cases hne : S.Nonempty
  · obtain ⟨i, hSub⟩ := subset_multiPart_of_isIndepSet hSi hne
    have hle : S.card ≤ (multiPart t n i).card := Finset.card_le_card hSub
    rw [card_multiPart] at hle
    rw [← hcard]
    exact hle
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty] at hcard
    omega

/-- **Every part of `X` is an independent set, so its size is at most `α(G[X])`.** -/
theorem le_indepCard_multiPart (i : Fin t) (X : Finset (Fin t × Fin n)) :
    (X ∩ multiPart t n i).card ≤ indepCard (multi t n) X :=
  le_indepCard_of_isIndepSet Finset.inter_subset_left
    (IsIndepSet.subset (isIndepSet_multiPart i) Finset.inter_subset_right)

/-- **THE COUNTING LEMMA: a vertex set of `multi t n` has size at most `t` times its independence
number.**  So `multi t n` maximises the ratio `|X| / α(G[X])` among graphs on `t * n` vertices whose
vertex set is split into `t` parts. -/
theorem card_le_mul_indepCard_multi (X : Finset (Fin t × Fin n)) :
    X.card ≤ t * indepCard (multi t n) X := by
  have h1 : X.card = ∑ i : Fin t, (X ∩ multiPart t n i).card := card_eq_sum_card_multiPart X
  have h2 : ∀ i : Fin t, (X ∩ multiPart t n i).card ≤ indepCard (multi t n) X :=
    fun i => le_indepCard_multiPart i X
  have h3 : (∑ i : Fin t, (X ∩ multiPart t n i).card) ≤ t * indepCard (multi t n) X := by
    calc (∑ i : Fin t, (X ∩ multiPart t n i).card)
        ≤ ∑ _i : Fin t, indepCard (multi t n) X :=
          Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t))) (fun i _ => h2 i)
      _ = t * indepCard (multi t n) X := by simp
  omega

/-! ## Part 2 — the deficiency of `multi t n` -/

/-- **THE VALUE OF THE HYPOTHESIS OF ERDŐS #73 ON THIS CLASS:**
`MaxDef (multi t n) = (t - 2) * n`, i.e. the maximum deficiency of a complete multipartite graph is
the total number of vertices in excess of two per part.

The upper bound is the counting lemma `card_le_mul_indepCard_multi`: every vertex set `X` satisfies
`|X| − 2 α(G[X]) ≤ (t − 2) α(G[X]) ≤ (t − 2) n`.  The lower bound is read off `X = V`, where the
independence number is at most `n` because an independent set lies in a part. -/
theorem maxDef_multi : MaxDef (multi t n) = (t - 2) * n := by
  have hcardV : ((Finset.univ : Finset (Fin t × Fin n)) : Finset (Fin t × Fin n)).card = t * n := by
    simp
  have hmul : (t - 2) * n = t * n - 2 * n := Nat.sub_mul t 2 n
  refine le_antisymm (maxDef_le (fun X => ?_)) ?_
  · have h1 := card_le_mul_indepCard_multi X
    have h2 := indepCard_le_multi X
    have h3 : (t - 2) * indepCard (multi t n) X
        = t * indepCard (multi t n) X - 2 * indepCard (multi t n) X := Nat.sub_mul t 2 _
    have h4 : (t - 2) * indepCard (multi t n) X
        ≤ (t - 2) * n := Nat.mul_le_mul_left (t - 2) h2
    unfold defOf
    omega
  · have h5 := le_maxDef (multi t n) (Finset.univ : Finset (Fin t × Fin n))
    have hα := indepCard_le_multi (Finset.univ : Finset (Fin t × Fin n))
    have hsub : t * n - 2 * n
        ≤ t * n - 2 * indepCard (multi t n) (Finset.univ : Finset (Fin t × Fin n)) :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hα) (t * n)
    unfold defOf at h5
    omega

/-- **ERDŐS'S HYPOTHESIS ON THIS CLASS**, read off `maxDef_multi`. -/
theorem locIndep_multi_iff {k : ℕ} : LocIndep k (multi t n) ↔ (t - 2) * n ≤ k := by
  rw [locIndep_iff_maxDef_le, maxDef_multi]

/-! ## Part 3 — the conclusion of Erdős #73 on this class -/

/-- **A GRAPH CONTAINING A TRIANGLE IS NOT BIPARTITE.**  This is the pigeonhole step of the
characterisation below: three pairwise adjacent vertices cannot receive pairwise distinct colours
out of `Fin 2`. -/
theorem not_isBipartite_of_tri {p q r : Fin t × Fin n} (hpq : (multi t n).Adj p q)
    (hqr : (multi t n).Adj q r) (hrp : (multi t n).Adj r p) :
    ¬ (multi t n).IsBipartite := by
  rintro ⟨d, hd⟩
  have hv : ∀ w : Fin t × Fin n, (d w).val < 2 := fun w => (d w).isLt
  have h1 : (d p).val ≠ (d q).val := fun h => hd hpq (Fin.ext h)
  have h2 : (d q).val ≠ (d r).val := fun h => hd hqr (Fin.ext h)
  have h3 : (d r).val ≠ (d p).val := fun h => hd hrp (Fin.ext h)
  omega

/-- **`multi t n` HAS NO EDGE WHEN IT HAS AT MOST ONE PART.** -/
theorem not_adj_multi_of_le_one (h : t ≤ 1) {p q : Fin t × Fin n} :
    ¬ (multi t n).Adj p q := by
  intro hadj
  have hne := multi_adj.mp hadj
  rcases Nat.eq_zero_or_pos t with hz | ht
  · subst hz
    exact hne (Fin.ext p.1.elim0)
  · have h1 : (p.1 : ℕ) = 0 := by have := p.1.isLt; omega
    have h2 : (q.1 : ℕ) = 0 := by have := q.1.isLt; omega
    exact hne (Fin.ext (by omega))

/-- **The parts of `multi t n` that survive the deletion of `X`**: the parts meeting `V \ X`. -/
def liveParts (t n : ℕ) (X : Finset (Fin t × Fin n)) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter (fun i => (multiPart t n i \ X).Nonempty)

@[simp] theorem mem_liveParts {X : Finset (Fin t × Fin n)} {i : Fin t} :
    i ∈ liveParts t n X ↔ (multiPart t n i \ X).Nonempty := by
  rw [liveParts, Finset.mem_filter]
  simp

/-- A vertex of `G − X` belongs to a live part. -/
theorem mem_liveParts_of_not_mem {X : Finset (Fin t × Fin n)} {p : Fin t × Fin n} (hp : p ∉ X) :
    p.1 ∈ liveParts t n X :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ⟨p, Finset.mem_sdiff.mpr ⟨mem_multiPart.mpr ⟨p.2, rfl⟩, hp⟩⟩⟩

/-- **A BIPARTITE RESIDUE HAS AT MOST TWO LIVE PARTS.**  Three live parts would contain three
pairwise adjacent vertices, i.e. a triangle, and `not_isBipartite_of_tri` rules that out.  The
colours of the live parts are injective into `Fin 2`, which is what the counting step needs. -/
theorem liveParts_le_two_of_isBipartite {X : Finset (Fin t × Fin n)}
    (h : (deleteFinset (multi t n) X).IsBipartite) : (liveParts t n X).card ≤ 2 := by
  obtain ⟨d, hd⟩ := h
  classical
  have hwit : ∀ i ∈ liveParts t n X, ∃ p : Fin t × Fin n, p ∉ X ∧ p.1 = i := by
    intro i hi
    obtain ⟨p, hp⟩ := mem_liveParts.mp hi
    refine ⟨p, (Finset.mem_sdiff.mp hp).2, ?_⟩
    exact mem_multiPart_iff.mp (Finset.mem_sdiff.mp hp).1
  have hcard := Finset.card_le_card_of_injOn
    (s := liveParts t n X)
    (t := (Finset.univ : Finset (Fin 2)))
    (f := fun i : Fin t =>
      if h : ∃ p : Fin t × Fin n, p ∉ X ∧ p.1 = i then d (Classical.choose h) else 0)
    (fun i _ => Finset.mem_univ _)
    (by
      intro i hi j hj hfeq
      have hpw : ∃ q : Fin t × Fin n, q ∉ X ∧ q.1 = i := hwit i hi
      have hqw : ∃ q : Fin t × Fin n, q ∉ X ∧ q.1 = j := hwit j hj
      change (if _ : ∃ q : Fin t × Fin n, q ∉ X ∧ q.1 = i then d (Classical.choose _) else 0)
        = (if _ : ∃ q : Fin t × Fin n, q ∉ X ∧ q.1 = j then d (Classical.choose _) else 0) at hfeq
      rw [dif_pos hpw, dif_pos hqw] at hfeq
      have hPX : (Classical.choose hpw : Fin t × Fin n) ∉ X := (Classical.choose_spec hpw).1
      have hQX : (Classical.choose hqw : Fin t × Fin n) ∉ X := (Classical.choose_spec hqw).1
      by_cases hij : i = j
      · exact hij
      · exact absurd hfeq (hd (deleteFinset_adj.mpr ⟨hPX, hQX, multi_adj.mpr
          (by rw [(Classical.choose_spec hpw).2, (Classical.choose_spec hqw).2]; exact hij)⟩)))
  simpa using hcard

/-- **The parts of `multi t n` destroyed by the deletion of `X`**: those contained in `X`. -/
def deadParts (t n : ℕ) (X : Finset (Fin t × Fin n)) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter (fun i => ¬ (multiPart t n i \ X).Nonempty)

@[simp] theorem mem_deadParts {X : Finset (Fin t × Fin n)} {i : Fin t} :
    i ∈ deadParts t n X ↔ multiPart t n i ⊆ X := by
  rw [deadParts, Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩ p hp
    by_contra hc
    exact h ⟨p, Finset.mem_sdiff.mpr ⟨hp, hc⟩⟩
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Finset.not_nonempty_iff_eq_empty.mpr (Finset.sdiff_eq_empty_iff_subset.mpr h)

/-- **Every part is live or dead**: for every part, either it still has a vertex after the
deletion of `X`, or it is contained in `X`. -/
theorem mem_liveParts_or_mem_deadParts (X : Finset (Fin t × Fin n)) (i : Fin t) :
    i ∈ liveParts t n X ∨ i ∈ deadParts t n X := by
  classical
  by_cases h : (multiPart t n i \ X).Nonempty
  · exact Or.inl (mem_liveParts.mpr h)
  · exact Or.inr (mem_deadParts.mpr
      (Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h)))

/-- **Every part is live or dead, and exactly one of the two holds**: the live and the dead parts
split the `t` parts. -/
theorem card_deadParts_add_liveParts (X : Finset (Fin t × Fin n)) :
    (liveParts t n X).card + (deadParts t n X).card = t := by
  have hunion : liveParts t n X ∪ deadParts t n X = (Finset.univ : Finset (Fin t)) :=
    Finset.Subset.antisymm
      (fun _ _ => Finset.mem_univ _)
      (fun i _ => Finset.mem_union.mpr (mem_liveParts_or_mem_deadParts X i))
  have hinter : liveParts t n X ∩ deadParts t n X = ∅ := by
    ext i
    rw [Finset.mem_inter, mem_liveParts, mem_deadParts]
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hx.1
      obtain ⟨hpP, hpX⟩ := Finset.mem_sdiff.mp hp
      exact absurd (hx.2 hpP) (fun h => hpX h)
    · intro hx
      exact absurd hx (fun h => by simpa using h)
  calc (liveParts t n X).card + (deadParts t n X).card
      = (liveParts t n X ∪ deadParts t n X).card + (liveParts t n X ∩ deadParts t n X).card :=
        (Finset.card_union_add_card_inter (liveParts t n X) (deadParts t n X)).symm
    _ = (liveParts t n X ∪ deadParts t n X).card := by
        rw [hinter, Finset.card_empty, Nat.add_zero]
    _ = t := by rw [hunion]; simp

/-- **AT MOST TWO SURVIVING PARTS MEANS BIPARTITE.**  If every vertex of `G − X` lies in one of two
parts, the colouring "first part versus second part" is a proper `2`-colouring. -/
theorem isBipartite_multi_of_cover {X : Finset (Fin t × Fin n)} {i j : Fin t}
    (h : ∀ p : Fin t × Fin n, p ∉ X → p.1 = i ∨ p.1 = j) :
    (deleteFinset (multi t n) X).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun p : Fin t × Fin n => if p.1 = i then 0 else 1)
    (fun {p q} hadj => ?_)⟩
  obtain ⟨hpX, hqX, hpq⟩ := deleteFinset_adj.mp hadj
  have hne : p.1 ≠ q.1 := multi_adj.mp hpq
  by_cases hpi : p.1 = i
  · have hqi : q.1 ≠ i := fun hc => hne (hpi.trans hc.symm)
    have hcp : (if p.1 = i then 0 else 1 : Fin 2) = 0 := if_pos hpi
    have hcq : (if q.1 = i then 0 else 1 : Fin 2) = 1 := if_neg hqi
    rw [hcp, hcq]
    decide
  · have hpj : p.1 = j := by
      rcases h p hpX with hpj | hpj
      · exact absurd hpj hpi
      · exact hpj
    have hqj : q.1 = i := by
      by_contra hcq
      have hq1 : q.1 = j := by
        rcases h q hqX with hqi | hqj
        · exact absurd hqi hcq
        · exact hqj
      exact hne (hpj.trans hq1.symm)
    have hcp : (if p.1 = i then 0 else 1 : Fin 2) = 1 := if_neg hpi
    have hcq : (if q.1 = i then 0 else 1 : Fin 2) = 0 := if_pos hqj
    rw [hcp, hcq]
    decide

/-- **A COMPLETE MULTIPARTITE GRAPH WITH AT MOST TWO PARTS IS BIPARTITE**, the `t ≤ 2` case of the
preceding lemma (`t ≤ 1` is edgeless, `t = 2` is `K_{n,n}`). -/
theorem isBipartite_multi_of_le_two (h : t ≤ 2) : (multi t n).IsBipartite := by
  by_cases h2 : t = 2
  · subst h2
    have hcov : ∀ p : Fin 2 × Fin n, p ∉ (∅ : Finset (Fin 2 × Fin n)) → p.1 = 0 ∨ p.1 = 1 := by
      intro p _
      have h1 : (p.1 : ℕ) ≤ 1 := Nat.le_of_lt_succ (by have := p.1.isLt; omega)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h | h
      · have hz : p.1 = 0 := Fin.ext h
        exact Or.inl hz
      · have ho : p.1 = 1 := Fin.ext h
        exact Or.inr ho
    have hb := isBipartite_multi_of_cover (X := (∅ : Finset (Fin 2 × Fin n)))
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) hcov
    rw [deleteFinset_empty] at hb
    exact hb
  · refine ⟨SimpleGraph.Coloring.mk (fun _ : Fin t × Fin n => (0 : Fin 2))
      (fun hadj => (not_adj_multi_of_le_one (by omega) hadj).elim)⟩

/-- **A finset of at most two elements is contained in a pair.** -/
theorem exists_pair_cover {α : Type*} [DecidableEq α] (D : Finset α) (hne : Nonempty α)
    (h : D.card ≤ 2) : ∃ i j : α, D ⊆ ({i} ∪ {j} : Finset α) := by
  by_cases h2 : D.card ≤ 1
  · letI : Nonempty α := hne
    obtain ⟨i, hi⟩ := Finset.card_le_one_iff_subset_singleton.mp h2
    exact ⟨i, i, hi.trans (by simp)⟩
  · have hlt2 : 2 ≤ D.card := Nat.succ_le_of_lt (Nat.not_le.mp h2)
    have heq : D.card = 2 := Nat.le_antisymm h hlt2
    obtain ⟨i, j, hij, hD⟩ := Finset.card_eq_two.mp heq
    refine ⟨i, j, ?_⟩
    rw [hD]
    exact fun _ h => h

/-- **THE CHARACTERISATION OF THE CONCLUSION ON THIS CLASS: `G − X` is bipartite exactly when the
vertices it keeps lie in at most two parts.** -/
theorem isBipartite_deleteFinset_multi_iff {X : Finset (Fin t × Fin n)} (ht : 1 ≤ t) :
    (deleteFinset (multi t n) X).IsBipartite ↔
      ∃ i j : Fin t, ∀ p : Fin t × Fin n, p ∉ X → p.1 = i ∨ p.1 = j := by
  constructor
  · intro h
    have hcard : (liveParts t n X).card ≤ 2 := liveParts_le_two_of_isBipartite h
    obtain ⟨i, j, hij⟩ := exists_pair_cover (liveParts t n X)
      (⟨⟨0, by omega⟩⟩ : Nonempty (Fin t)) hcard
    refine ⟨i, j, fun p hp => ?_⟩
    have hp1 : p.1 ∈ {i, j} := hij (mem_liveParts_of_not_mem hp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hp1
  · rintro ⟨i, j, h⟩
    exact isBipartite_multi_of_cover h

/-! ## Part 4 — the value of the conclusion, and a new instance of the headline theorem -/

/-- **THE EXACT VALUE OF THE CONCLUSION OF ERDŐS #73 ON THE COMPLETE MULTIPARTITE GRAPHS:**
`CloseToBipartite m (multi t n) ↔ (t − 2) * n ≤ m`.

(⇒) a bipartite residue has at most two live parts, hence at least `t − 2` dead parts, and each of
them has `n` vertices inside `X`.  (⇐) deleting `t − 2` whole parts leaves the vertices of two
parts, which is bipartite by `isBipartite_multi_of_cover`. -/
theorem closeToBipartite_iff_multi {m : ℕ} :
    CloseToBipartite m (multi t n) ↔ (t - 2) * n ≤ m := by
  constructor
  · rintro ⟨X, hXm, hXb⟩
    have hlive : (liveParts t n X).card ≤ 2 := liveParts_le_two_of_isBipartite hXb
    have hsplit := card_deadParts_add_liveParts X
    have hDcard : t - 2 ≤ (deadParts t n X).card := by omega
    have hsub : Finset.biUnion (deadParts t n X) (multiPart t n) ⊆ X := by
      intro p hp
      obtain ⟨i, hi, hi2⟩ := Finset.mem_biUnion.mp hp
      exact (mem_deadParts.mp hi) hi2
    have hbi : ∀ (D : Finset (Fin t)), (Finset.biUnion D (multiPart t n)).card = D.card * n := by
      intro D
      induction D using Finset.induction_on with
      | empty => simp
      | @insert i D hi ih =>
          have hdis : Disjoint (multiPart t n i) (Finset.biUnion D (multiPart t n)) :=
            Finset.disjoint_left.2 fun p hp hq => by
              obtain ⟨j, hj, hjp⟩ := Finset.mem_biUnion.mp hq
              have h1 : p.1 = i := mem_multiPart_iff.mp hp
              have h2 : p.1 = j := mem_multiPart_iff.mp hjp
              have hd' : i ∈ D := by
                rw [h1.symm, h2]
                exact hj
              exact hi hd'
          calc (Finset.biUnion (insert i D) (multiPart t n)).card
              = (multiPart t n i ∪ Finset.biUnion D (multiPart t n)).card := by
                rw [Finset.biUnion_insert]
            _ = (multiPart t n i).card + (Finset.biUnion D (multiPart t n)).card := by
                have hz : ((multiPart t n i) ∩ (Finset.biUnion D (multiPart t n))).card = 0 :=
                  Finset.card_eq_zero.mpr (Finset.disjoint_iff_inter_eq_empty.mp hdis)
                rw [(Finset.card_union_add_card_inter (multiPart t n i)
                    (Finset.biUnion D (multiPart t n))).symm, hz, Nat.add_zero]
            _ = n + (Finset.biUnion D (multiPart t n)).card := by rw [card_multiPart]
            _ = n + D.card * n := by rw [ih]
            _ = (insert i D).card * n := by
              rw [Finset.card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm]
    have hcard : (deadParts t n X).card * n
        ≤ (Finset.biUnion (deadParts t n X) (multiPart t n)).card := by
      rw [hbi]
    have hle : (t - 2) * n ≤ X.card := by
      calc (t - 2) * n = n * (t - 2) := Nat.mul_comm _ _
        _ ≤ n * (deadParts t n X).card := Nat.mul_le_mul_left _ hDcard
        _ = (deadParts t n X).card * n := Nat.mul_comm _ _
        _ ≤ (Finset.biUnion (deadParts t n X) (multiPart t n)).card := hcard
        _ ≤ X.card := Finset.card_le_card hsub
    omega
  · intro hle
    by_cases ht2 : t ≤ 2
    · exact ⟨∅, Nat.zero_le _, isBipartite_delete (isBipartite_multi_of_le_two ht2)⟩
    · have ht3 : 3 ≤ t := by omega
      set i₀ : Fin t := ⟨t - 2, by omega⟩ with hi₀
      set j₀ : Fin t := ⟨t - 1, by omega⟩ with hj₀
      set D : Finset (Fin t) := ((Finset.univ : Finset (Fin t)).erase i₀).erase j₀ with hD
      have hij' : (i₀ : Fin t) ≠ j₀ := by
        intro hc
        have hv := congrArg Fin.val hc
        simp only [Fin.val_mk, i₀, j₀] at hv
        omega
      have hDcard : D.card = t - 2 := by
        rw [hD, Finset.card_erase_of_mem (a := j₀) (s := (Finset.univ : Finset (Fin t)).erase i₀)
          (by rw [Finset.mem_erase]; exact ⟨Ne.symm hij', Finset.mem_univ _⟩)]
        simp
        omega
      set X : Finset (Fin t × Fin n) := Finset.biUnion D (multiPart t n) with hX
      have hXcard : X.card ≤ D.card * n :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun i _ => by rw [card_multiPart])
      refine ⟨X, ?_, ?_⟩
      · calc X.card ≤ D.card * n := hXcard
          _ = (t - 2) * n := by rw [hDcard]
          _ ≤ m := hle
      · refine isBipartite_multi_of_cover (X := X) (i := i₀) (j := j₀) ?_
        intro p hpX
        have hpD : p.1 ∉ D := by
          intro hpD
          exact hpX (Finset.mem_biUnion.mpr ⟨p.1, hpD, mem_multiPart.mpr ⟨p.2, rfl⟩⟩)
        by_contra hcon
        exact hpD (Finset.mem_erase_of_ne_of_mem (fun h => hcon (Or.inr h))
          (Finset.mem_erase_of_ne_of_mem (fun h => hcon (Or.inl h)) (Finset.mem_univ _)))

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE OPTIMAL CONSTANT `f(k) = k`:** on the complete
multipartite graphs, Erdős's hypothesis forces the conclusion with the constant `k`.  No bound on
the odd girth, the packing weight, the degree or the connectivity is used, and the constant is the
same as in the other identity instances of the development (rounds 98, 100, 104, 105). -/
theorem erdos73On_of_multi {k : ℕ} (hG : LocIndep k (multi t n)) : CloseToBipartite k (multi t n) := by
  refine (closeToBipartite_iff_multi (m := k)).mpr ?_
  have h' := locIndep_multi_iff.mp hG
  omega

/-- The same instance in the house style, quantified over all finite vertex types. -/
theorem erdos73On_of_multi_univ (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (t n : ℕ),
      LocIndep k (multi t n) → CloseToBipartite k (multi t n) := by
  intro W instW t n hG
  exact erdos73On_of_multi hG

/-- **THE CONSTANT `k` OF THE NEW INSTANCE IS OPTIMAL**: the least `m` for which Erdős #73 holds on
`multi t n` is exactly `(t − 2) * n`; no constant below it works.  The witness is
`multi 3 1 = K_3`, where the hypothesis `LocIndep 1` holds and the conclusion needs `m ≥ 1`. -/
theorem erdos73On_of_multi_optimal {m : ℕ} :
    (∀ k : ℕ, LocIndep k (multi t n) → CloseToBipartite m (multi t n)) ↔ (t - 2) * n ≤ m := by
  constructor
  · intro h
    by_cases hc : m < (t - 2) * n
    · have hle := h ((t - 2) * n) (locIndep_multi_iff.mpr (le_refl _))
      exact absurd ((closeToBipartite_iff_multi (m := m)).mp hle) (Nat.not_le_of_gt hc)
    · omega
  · rintro hk k hG
    exact (closeToBipartite_iff_multi (m := m)).mpr hk

/-- **No smaller budget works on this class.** -/
theorem not_closeToBipartite_multi {m : ℕ} (h : m < (t - 2) * n) :
    ¬ CloseToBipartite m (multi t n) := by
  rintro ⟨X, hXm, hXb⟩
  exact Nat.not_lt_of_ge ((closeToBipartite_iff_multi (m := m)).mp ⟨X, hXm, hXb⟩) h

end Multi

end

end JSP90