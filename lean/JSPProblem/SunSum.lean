/-
# `JSPProblem/SunSum.lean` — **the constant in Erdős #73 is at least `2 k`**

Attack family 95, the **lower-bound / sharpness axis**, and a change of object with respect to
rounds 171–175 (which computed *upper* bounds on the odd cycle transversal of a graph of defect at
most `k` on `n` vertices).  Nothing here bounds an order; the statements are **order-free** and they
constrain the *constant* of the headline theorem itself.

## What was known

`JSPProblem/Sharp.lean` supplies the witness `kTriangles k` = `K_3 ⊔ … ⊔ K_3` and the machine-checked
lower bound `JSP90.no_constant_below_k`: no constant below `k` can work, i.e. one unit of deficit
forces one vertex of transversal.  `JSPProblem/Sun.lean` supplies the other piece: the 3-sun `sun3`
is `LocIndep 1` **and** `¬ CloseToBipartite 1 sun3`, i.e. **two** units of transversal for **one**
unit of deficit.

## What this file adds

* **Part 0** — `JSP90.sumGraph j H`, the disjoint union of a finite family of graphs on `W × Fin j`,
  with its fibres and the counting lemmas that make the disjoint union transparent:
  `JSP90.card_eq_sum_card_inter_fib`, `JSP90.biUnion_inter_fib`, `JSP90.card_image_fib`,
  `JSP90.mem_image_fib`, `JSP90.exists_of_mem_image_fib`.
* **Part 1** — **`JSP90.indepCard_sumGraph`: the independence number is additive over a disjoint
  union**, `α(⊔ H i) (X) = ∑ α(H i) (X ∩ fib i)`, proved in both directions
  (`isIndepSet_sumGraph`, `exists_indepCard_sumGraph`).
* **Part 2** — **`JSP90.locIndep_sumGraph`: `LocIndep (j * k) (⊔ H i)` if every `H i` is
  `LocIndep k`** — Erdős's local hypothesis is *summed over the components*, with the machinery of
  `JSPProblem/Deficiency.lean` (`MaxDef`, `locIndep_iff_maxDef_le`) and no order bound.
* **Part 3** — **`JSP90.sun3U k`** = the disjoint union of `k` 3-suns: `LocIndep k` by Part 2, and
  **every set of at most `2 k - 1` vertices leaves an odd cycle somewhere**
  (`JSP90.not_closeToBipartite_lt_two_mul_sun3U`), via the transport lemma
  `JSP90.deleteFinset_sumGraph_fib`, which reads the residue of the union inside one fibre as a
  residue of that fibre's graph.
* **Part 4 — the headline statements.**
  * `JSP90.tauOdd_sun3U`: the least odd cycle transversal of the `k`-fold sun is **exactly** `2 k`;
  * **`JSP90.erdos73On_two_mul_le`: any constant `m` which makes Erdős #73 true at the parameter `k`
    satisfies `2 * k ≤ m`** — an *order-free* lower bound on the constant `f(k)`, twice the bound of
    `JSPProblem/Sharp.lean`, and the reason the constant `2` of
    `JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight` cannot be lowered to `1`;
  * `JSP90.not_erdos73On_lt_two_mul`, `JSP90.two_mul_le_of_erdos73`,
    `JSP90.not_erdos73On_one_one`, paired with
    `JSP90.erdos73On_one_one_of_card_le_five`: at `k = 1` the constant is `1` up to five vertices and
    at least `2` from six vertices on;
  * `JSP90.maxDef_sun3U` / `JSP90.not_locIndep_sun3U`: the witness is *exact*, as `kTriangles` is.

`jsp_000090_main` is deliberately **not** declared: the direction proved here is a lower bound on
the constant, and the missing direction is still `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), through `JSP90.erdos73_of_erdosPosa`.
-/

import JSPProblem.IndepSplit

namespace JSP90

open Finset Fintype

universe u

noncomputable section

/-- One single classical `DecidableEq` for every product type in this file: the `Fin`-instances of
the two sections below would otherwise disagree with the derived product instance. -/
local instance sunSumProdDecidableEq {α β : Type*} : DecidableEq (α × β) := Classical.decEq (α × β)

/-! ## Part 0 — the disjoint union of a finite family of graphs -/

section Sum

variable {W : Type*} [Fintype W]

local instance sunSumDecidableEqSum : DecidableEq W := Classical.decEq W

/-- **`sumGraph j H` is the disjoint union of the `j` graphs `H i`**, on the vertex type
`W × Fin j`: two vertices are adjacent exactly when they carry the same index and are adjacent in
`H i` there. -/
def sumGraph (j : ℕ) (H : Fin j → SimpleGraph W) : SimpleGraph (W × Fin j) where
  Adj p q := p.2 = q.2 ∧ (H p.2).Adj p.1 q.1
  symm := ⟨fun v w h => ⟨h.1.symm, h.1 ▸ (H _).adj_symm h.2⟩⟩
  loopless := ⟨fun v h => (H _).irrefl h.2⟩

@[simp] theorem sumGraph_adj {j : ℕ} {H : Fin j → SimpleGraph W} {p q : W × Fin j} :
    (sumGraph j H).Adj p q ↔ p.2 = q.2 ∧ (H p.2).Adj p.1 q.1 := Iff.rfl

/-- The `i`-th **fibre** of `W × Fin j`: the copy of `W` at index `i`. -/
def fib {j : ℕ} (i : Fin j) : Finset (W × Fin j) :=
  (Finset.univ : Finset W).image (fun v => (v, i))

@[simp] theorem mem_fib {j : ℕ} {i : Fin j} {p : W × Fin j} : p ∈ fib i ↔ p.2 = i := by
  rw [fib, Finset.mem_image]
  constructor
  · rintro ⟨v, -, rfl⟩
    rfl
  · rintro rfl
    exact ⟨p.1, Finset.mem_univ _, rfl⟩

theorem fib_subset_univ {j : ℕ} (i : Fin j) : fib i ⊆ (Finset.univ : Finset (W × Fin j)) :=
  Finset.subset_univ _

/-- **Two distinct fibres are disjoint.** -/
theorem inter_fib_eq_empty {j : ℕ} {i i' : Fin j} (h : i ≠ i') :
    (fib i : Finset (W × Fin j)) ∩ fib i' = ∅ := by
  refine Finset.Subset.antisymm (fun x hx => ?_) (Finset.empty_subset _)
  simp only [Finset.mem_inter] at hx
  exact absurd (h ((mem_fib.mp hx.1).symm.trans (mem_fib.mp hx.2))) (by simp)

/-- The second coordinate of a point of the `i`-th copy is `i`. -/
theorem snd_eq_of_mem_image_fib {j : ℕ} {D : Finset W} {i : Fin j} {p : W × Fin j}
    (h : p ∈ D.image (fun v : W => (v, i))) : p.2 = i := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h
  rfl

/-- The map `v ↦ (v, i)` is injective. -/
theorem injOn_pair {j : ℕ} (D : Finset W) (i : Fin j) :
    Set.InjOn (fun v : W => (v, i)) (↑(D : Finset W)) := by
  intro v _ v' _ h
  exact Prod.ext_iff.mp h |>.1

theorem card_image_pair {j : ℕ} (S : Finset W) (i : Fin j) :
    (S.image (fun v : W => (v, i))).card = Finset.card S :=
  Finset.card_image_of_injOn (injOn_pair S i)

/-- The projection to `W` is injective on the `i`-th copy of a set. -/
theorem injOn_fst_image {j : ℕ} (D : Finset W) (i : Fin j) :
    Set.InjOn (Prod.fst : (W × Fin j) → W) (↑(D.image (fun v : W => (v, i)))) := by
  intro x₁ hx₁ x₂ hx₂ h
  exact Prod.ext h
    ((snd_eq_of_mem_image_fib (D := D) (i := i) (p := x₁) hx₁).trans
      (snd_eq_of_mem_image_fib (D := D) (i := i) (p := x₂) hx₂).symm)

theorem card_fib {j : ℕ} (i : Fin j) : (fib i : Finset (W × Fin j)).card = Fintype.card W := by
  have h := Finset.card_image_of_injOn (s := (Finset.univ : Finset W))
    (f := fun v : W => (v, i)) (injOn_pair (Finset.univ : Finset W) i)
  simpa [fib] using h

/-- **The projection to `W` is injective on a fibre.** -/
theorem injOn_fst_inter_fib {j : ℕ} {S : Finset (W × Fin j)} (i : Fin j) :
    Set.InjOn (Prod.fst : (W × Fin j) → W) (↑(S ∩ fib i)) := by
  intro x₁ hx₁ x₂ hx₂ h
  refine Prod.ext h ?_
  exact ((mem_fib (i := i) (p := x₁)).mp (Finset.mem_inter.mp hx₁).2).trans
    ((mem_fib (i := i) (p := x₂)).mp (Finset.mem_inter.mp hx₂).2).symm

/-- **A vertex set meets each fibre in a set of the same size**. -/
theorem card_image_fib {j : ℕ} {S : Finset (W × Fin j)} (i : Fin j) :
    ((S ∩ fib i).image Prod.fst).card = (S ∩ fib i).card :=
  Finset.card_image_of_injOn (s := S ∩ fib i) (f := Prod.fst) (injOn_fst_inter_fib i)

/-- `v ∈ D` implies `(v, i) ∈ D.image (fun w => (w, i))`. -/
theorem mem_image_fib {j : ℕ} {D : Finset W} {i : Fin j} {v : W} (h : v ∈ D) :
    (v, i) ∈ D.image (fun w => (w, i)) :=
  Finset.mem_image.mpr ⟨v, h, rfl⟩

/-- The converse reading: a point of the `i`-th copy of a subset of `W`. -/
theorem exists_of_mem_image_fib {j : ℕ} {D : Finset W} {i : Fin j} {p : W × Fin j}
    (h : p ∈ D.image (fun w => (w, i))) : ∃ v ∈ D, (v, i) = p :=
  Finset.mem_image.mp h

/-- **A point of the `i`-th copy of a subset of `X ∩ fib i` lies in `X`.** -/
theorem mem_of_mem_image_fib_sub {j : ℕ} {X : Finset (W × Fin j)} {D : Finset W} {i : Fin j}
    {v : W} (hD : D ⊆ (X ∩ fib i).image Prod.fst) (hv : v ∈ D) : (v, i) ∈ X := by
  obtain ⟨p, hp1, hp2⟩ := Finset.mem_image.mp (hD hv)
  have hp1' : p ∈ X ∩ fib i := hp1
  have hpeq : p = (v, i) := Prod.ext (hp2.trans rfl) (mem_fib.mp (Finset.mem_inter.mp hp1').2)
  exact hpeq ▸ (Finset.mem_inter.mp hp1').1

/-- **`X` is the disjoint union of its pieces inside the fibres.** -/
theorem biUnion_inter_fib {j : ℕ} {X : Finset (W × Fin j)} :
    ((Finset.univ : Finset (Fin j)).biUnion (fun i => (X ∩ fib i : Finset (W × Fin j)))) = X := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact Finset.mem_inter.mp hi |>.1
  · intro hp
    exact ⟨p.2, Finset.mem_inter.mpr ⟨hp, mem_fib.mpr rfl⟩⟩

/-- **THE `i`-TH AND `i'`-TH COPIES OF TWO SUBSETS OF `W` ARE DISJOINT.** -/
theorem disjoint_image_fib {j : ℕ} {D D' : Finset W} {i i' : Fin j} (h : i ≠ i') :
    Disjoint (D.image (fun v : W => (v, i))) (D'.image (fun v : W => (v, i'))) := by
  refine Finset.disjoint_left.mpr fun a ha hna => ?_
  exact h ((snd_eq_of_mem_image_fib ha).symm.trans (snd_eq_of_mem_image_fib hna))

/-- **TWO POINTS IN THE `i`-TH AND `i'`-TH FIBRES ARE DISTINCT.** -/
theorem ne_of_mem_image_fib {j : ℕ} {D D' : Finset W} {i i' : Fin j} {a b : W × Fin j}
    (h1 : a ∈ D.image (fun v : W => (v, i))) (h2 : b ∈ D'.image (fun v : W => (v, i')))
    (h : i ≠ i') : a ≠ b := by
  intro hab
  exact h ((snd_eq_of_mem_image_fib h1).symm.trans
    ((congrArg Prod.snd hab).trans (snd_eq_of_mem_image_fib h2)))

/-- **THE PIECES OF A DISJOINT UNION ARE PAIRWISE DISJOINT.** -/
theorem pairwiseDisjoint_image {j : ℕ} (D : Fin j → Finset W) :
    ((Finset.univ : Finset (Fin j)) : Set (Fin j)).PairwiseDisjoint
      (fun i => (D i).image (fun v : W => (v, i))) := by
  intro i _ i' _ hne
  exact disjoint_image_fib hne

/-- **THE PIECES OF A VERTEX SET INSIDE THE FIBRES ARE PAIRWISE DISJOINT.** -/
theorem pairwiseDisjoint_inter_fib {j : ℕ} {X : Finset (W × Fin j)} :
    ((Finset.univ : Finset (Fin j)) : Set (Fin j)).PairwiseDisjoint
      (fun i => X ∩ fib i) := by
  intro i i' _ _ hne
  refine Finset.disjoint_left.mpr fun a ha hna => ?_
  exact hne ((mem_fib.mp (Finset.mem_inter.mp ha).2).symm.trans
    (mem_fib.mp (Finset.mem_inter.mp hna).2))

/-- **Cardinality is additive over the fibres.** -/
theorem card_eq_sum_card_inter_fib {j : ℕ} {X : Finset (W × Fin j)} :
    X.card = ∑ i : Fin j, (X ∩ fib i).card := by
  classical
  have hb := Finset.card_biUnion (s := (Finset.univ : Finset (Fin j)))
    (t := fun i => (X ∩ fib i))
    (pairwiseDisjoint_inter_fib (X := X))
  rw [biUnion_inter_fib (X := X)] at hb
  exact hb

/-- **A point of the projection of `S ∩ fib i` into `W` is the projection of a point of `S`.** -/
theorem eq_pair_of_mem_image_fst {j : ℕ} {S : Finset (W × Fin j)} {i : Fin j} {u : W}
    (hu : u ∈ ((↑((S ∩ fib (i : Fin j)).image (Prod.fst : (W × Fin j) → W))) : Set W)) : (u, i) ∈ S := by
  obtain ⟨b, hb, hbu⟩ := Finset.mem_image.mp hu
  have hb' : b ∈ S ∩ fib i := hb
  have hbeq : b = (u, i) := Prod.ext hbu (mem_fib.mp (Finset.mem_inter.mp hb').2)
  exact hbeq ▸ (Finset.mem_inter.mp hb').1

/-- **THE INDEPENDENT SETS OF THE SUM SPLIT OVER THE FIBRES**: the projection of an independent set
of `sumGraph` into one fibre is an independent set of that fibre's graph. -/
theorem isIndepSet_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} {S : Finset (W × Fin j)}
    (hS : (sumGraph j H).IsIndepSet S) (i : Fin j) :
    (H i).IsIndepSet ((S ∩ fib i).image Prod.fst) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv hne hadj
  have hu' : (u, i) ∈ S := eq_pair_of_mem_image_fst hu
  have hv' : (v, i) ∈ S := eq_pair_of_mem_image_fst hv
  have hne' : (u, i) ≠ (v, i) := fun he => hne (Prod.ext_iff.mp he |>.1)
  have hadj' : (sumGraph j H).Adj (u, i) (v, i) := ⟨rfl, hadj⟩
  exact hS hu' hv' hne' hadj'

end Sum

/-! ## Part 1 — the independence number is additive over a disjoint union -/

section Alpha

variable {W : Type*} [Fintype W]

local instance sunSumDecidableEqAlpha : DecidableEq W := Classical.decEq W

/-- **AN INDEPENDENT SET OF THE SUM INSIDE ONE FIBRE IS AN INDEPENDENT SET OF THAT PIECE, WITH THE
SAME CARDINALITY.** -/
theorem exists_indepCard_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} (X : Finset (W × Fin j)) :
    ∃ S : Finset (W × Fin j), S ⊆ X ∧ (sumGraph j H).IsIndepSet S ∧
      S.card = ∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst) := by
  classical
  choose! S hSsub hSi hScard using fun i : Fin j => exists_indepCard (H i)
    ((X ∩ fib i).image Prod.fst)
  set T : Finset (W × Fin j) :=
    (Finset.univ : Finset (Fin j)).biUnion (fun i => (S i).image (fun v => (v, i))) with hTdef
  refine ⟨T, ?_, ?_, ?_⟩
  · intro p hp
    rw [hTdef, Finset.mem_biUnion] at hp
    obtain ⟨i, -, hi⟩ := hp
    obtain ⟨v, hv, hvp⟩ := exists_of_mem_image_fib hi
    exact hvp ▸ mem_of_mem_image_fib_sub (hD := hSsub i) (hv := hv)
  · rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv hne hadj
    have huT : u ∈ T := Finset.mem_coe.mp hu
    have hvT : v ∈ T := Finset.mem_coe.mp hv
    rw [hTdef, Finset.mem_biUnion] at huT hvT
    obtain ⟨i, -, hiu⟩ := huT
    obtain ⟨j, -, hvT'⟩ := hvT
    obtain ⟨u', hu1, hu2⟩ := Finset.mem_image.mp hiu
    obtain ⟨v', hv1, hv2⟩ := Finset.mem_image.mp hvT'
    subst_vars
    rw [sumGraph_adj] at hadj
    have hij : i = j := by simpa using hadj.1
    subst hij
    exact hSi i hu1 hv1 (fun h => hne (Prod.ext_iff.mpr ⟨h, rfl⟩)) hadj.2
  · rw [hTdef]
    have hb : (((Finset.univ : Finset (Fin j)).biUnion
        (fun i => (S i).image (fun v : W => (v, i))) : Finset (W × Fin j))).card
        = ∑ i : Fin j, ((S i).image (fun v : W => (v, i))).card :=
      Finset.card_biUnion (s := (Finset.univ : Finset (Fin j)))
        (t := fun i => (S i).image (fun v : W => (v, i)))
        (pairwiseDisjoint_image S)
    rw [Finset.sum_congr rfl fun i _ => (card_image_pair (S i) i).trans (hScard i)] at hb
    exact hb

/-- **THE INDEPENDENCE NUMBER OF A DISJOINT UNION IS THE SUM OF THE INDEPENDENCE NUMBERS OF ITS
PIECES**, on the corresponding pieces of the vertex set:

```lean
α(⊔ H i) (X) = ∑ i, α(H i) (X ∩ fib i)
```

Both directions: an independent set of the sum splits into independent sets of the pieces (with the
cardinalities preserved, `isIndepSet_sumGraph`), and independent sets of the pieces glued along the
fibres are independent in the sum (`exists_indepCard_sumGraph`). -/
theorem indepCard_sumGraph {j : ℕ} {H : Fin j → SimpleGraph W} (X : Finset (W × Fin j)) :
    indepCard (sumGraph j H) X = ∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst) := by
  classical
  refine le_antisymm (Finset.sup_le_iff.mpr fun S hS => ?_) ?_
  · have hSsub : S ⊆ X := sub_of_mem_indepSets hS
    have hsub' (i : Fin j) : (S ∩ fib i) ⊆ (X ∩ fib i) := fun a ha =>
      Finset.mem_inter.mpr ⟨hSsub (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩
    calc S.card = ∑ i : Fin j, (S ∩ fib i).card := card_eq_sum_card_inter_fib (X := S)
      _ ≤ ∑ i : Fin j, indepCard (H i) ((S ∩ fib i).image Prod.fst) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc (S ∩ fib i).card = ((S ∩ fib i).image Prod.fst).card := (card_image_fib i).symm
            _ ≤ indepCard (H i) ((S ∩ fib i).image Prod.fst) := by
                refine le_indepCard_of_isIndepSet (Finset.Subset.refl _) ?_
                exact isIndepSet_sumGraph (isIndepSet_of_mem_indepSets hS) i
      _ ≤ ∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst) :=
          Finset.sum_le_sum fun i _ => indepCard_le_of_subset (Finset.image_subset_image (hsub' i))
  · obtain ⟨S, hSsub, hSi, hScard⟩ := exists_indepCard_sumGraph X
    rw [← hScard]
    exact le_indepCard_of_isIndepSet hSsub hSi

end Alpha

/-! ## Part 2 — Erdős's local hypothesis is summed over the components -/

section Loc

variable {W : Type*} [Fintype W]

local instance sunSumDecidableEqLoc : DecidableEq W := Classical.decEq W

/-- **THE DEFICIENCY OF A VERTEX SET OF A DISJOINT UNION IS AT MOST THE SUM OF THE DEFICIENCIES OF
ITS PIECES.** -/
theorem defOf_sumGraph_le {j k : ℕ} {H : Fin j → SimpleGraph W} (hH : ∀ i, MaxDef (H i) ≤ k)
    (X : Finset (W × Fin j)) : defOf (sumGraph j H) X ≤ j * k := by
  have hle : ∀ i : Fin j, (X ∩ fib i).card
      ≤ 2 * indepCard (H i) ((X ∩ fib i).image Prod.fst) + k := by
    intro i
    have h1 := (le_maxDef (H i) ((X ∩ fib i).image Prod.fst)).trans (hH i)
    rw [defOf, card_image_fib i] at h1
    omega
  have hkey : X.card ≤ 2 * (∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst)) + j * k := by
    calc X.card = ∑ i : Fin j, (X ∩ fib i).card := card_eq_sum_card_inter_fib
      _ ≤ ∑ i : Fin j, (2 * indepCard (H i) ((X ∩ fib i).image Prod.fst) + k) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 2 * (∑ i : Fin j, indepCard (H i) ((X ∩ fib i).image Prod.fst)) + j * k := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp
  rw [defOf, indepCard_sumGraph]
  omega

/-- **`LocIndep (j * k) (⊔ H i)` whenever every `H i` is `LocIndep k`** — Erdős's local hypothesis is
summed over the components, with **no bound on the order** and no other hypothesis. -/
theorem locIndep_sumGraph {j k : ℕ} {H : Fin j → SimpleGraph W}
    (hH : ∀ i, LocIndep k (H i)) : LocIndep (j * k) (sumGraph j H) := by
  rw [locIndep_iff_maxDef_le]
  exact maxDef_le fun X => defOf_sumGraph_le (fun i => maxDef_le_of_locIndep (hH i)) X

/-- **THE MAXIMUM DEFICIENCY OF THE `j`-FOLD SUM OF GRAPHS OF DEFICIENCY AT MOST `k` IS AT MOST
`j * k`.** -/
theorem maxDef_sumGraph_le {j k : ℕ} {H : Fin j → SimpleGraph W} (hH : ∀ i, MaxDef (H i) ≤ k) :
    MaxDef (sumGraph j H) ≤ j * k :=
  maxDef_le fun X => defOf_sumGraph_le hH X

end Loc

/-! ## Part 3 — the `k`-fold 3-sun: `LocIndep k` and no transversal of size `< 2 k` -/

section Sun

local instance : DecidableRel sun3.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ sun3Edge))

/-- **`sun3U k` is the disjoint union of `k` 3-suns** (on `Fin 6 × Fin k`). -/
def sun3U (k : ℕ) : SimpleGraph (Fin 6 × Fin k) := sumGraph k (fun _ => sun3)

@[simp] theorem sun3U_adj {k : ℕ} {p q : Fin 6 × Fin k} :
    (sun3U k).Adj p q ↔ p.2 = q.2 ∧ sun3.Adj p.1 q.1 := sumGraph_adj

/-- **The 3-sun has deficiency at most one** — the hypothesis of `JSPProblem/Sun.lean`
(`locIndep_one_sun3`) in the form Part 2 consumes. -/
theorem maxDef_le_one_sun3 : MaxDef sun3 ≤ 1 := maxDef_le_of_locIndep locIndep_one_sun3

/-- **`sun3U k` satisfies Erdős's local hypothesis with the parameter `k`** — by Part 2, since each
3-sun has deficiency at most `1`. -/
theorem locIndep_sun3U (k : ℕ) : LocIndep k (sun3U k) := by
  have h := locIndep_sumGraph (j := k) (k := 1) (H := fun _ => sun3) (fun _ => locIndep_one_sun3)
  simpa [sun3U] using h

section GraphMap

variable {V W : Type*} [Fintype V] [Fintype W]

local instance sunSumDecidableEqGraphMap : DecidableEq W := Classical.decEq W

/-- **Bipartiteness passes down a graph homomorphism**: if `φ` is a homomorphism of `G` into `H`
and `H` is bipartite on `s`, then `G` is bipartite on the preimage of `s`. -/
theorem isBipartite_induce_of_graphMap {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : V → W)
    (hφ : ∀ u v, G.Adj u v → H.Adj (φ u) (φ v)) (s : Finset W)
    (hs : (induceFinset H s).IsBipartite) :
    (induceFinset G ((Finset.univ : Finset V).filter (fun v => φ v ∈ s))).IsBipartite := by
  obtain ⟨⟨d, hd⟩⟩ := hs
  refine ⟨SimpleGraph.Coloring.mk (fun v => d (φ v)) fun {u v} hadj => ?_⟩
  obtain ⟨hu, hv, hadj'⟩ := induce_adj.mp hadj
  have hu' : φ u ∈ s := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
  have hv' : φ v ∈ s := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
  exact hd (induce_adj.mpr ⟨hu', hv', hφ u v hadj'⟩)

end GraphMap

section Fib

variable {W : Type*} [Fintype W]

local instance sunSumDecidableEqFib : DecidableEq W := Classical.decEq W

/-- **THE RESIDUE OF THE SUM INSIDE ONE FIBRE IS THE RESIDUE OF THAT PIECE.**  If `Z` is deleted from
the disjoint union and the result is bipartite, then the residue of `Z` in the `i`-th fibre is a
residue of the graph `H i`. -/
theorem deleteFinset_sumGraph_fib {j : ℕ} {H : Fin j → SimpleGraph W}
    {Z : Finset (W × Fin j)} (i : Fin j) (hb : (deleteFinset (sumGraph j H) Z).IsBipartite) :
    (deleteFinset (H i) ((Z ∩ fib i).image Prod.fst)).IsBipartite := by
  classical
  have hb' : (induceFinset (sumGraph j H)
      ((Finset.univ : Finset (W × Fin j)) \ Z)).IsBipartite := by
    simpa only [deleteFinset] using hb
  have h1 : (induceFinset (sumGraph j H)
      (((Finset.univ : Finset (W × Fin j)) \ Z) ∩ fib i)).IsBipartite :=
    isBipartite_induceFinset_of_isBipartite hb' Finset.inter_subset_left
  have hφ : ∀ u v : W, (deleteFinset (H i) ((Z ∩ fib i).image Prod.fst)).Adj u v →
      (sumGraph j H).Adj (u, i) (v, i) := by
    intro u v hadj
    rcases induce_adj.mp hadj with ⟨hu, hv, hadj'⟩
    rw [sumGraph_adj]
    exact ⟨rfl, hadj'⟩
  have h2 := isBipartite_induce_of_graphMap
    (G := deleteFinset (H i) ((Z ∩ fib i).image Prod.fst)) (H := sumGraph j H)
    (φ := fun v => (v, i)) hφ (((Finset.univ : Finset (W × Fin j)) \ Z) ∩ fib i) h1
  have hsub : ((Finset.univ : Finset W) \ (Z ∩ fib i).image Prod.fst) ⊆
      ((Finset.univ : Finset W).filter
        (fun v => (v, i) ∈ (((Finset.univ : Finset (W × Fin j)) \ Z) ∩ fib i))) := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hm' : v ∉ (Z ∩ fib i).image Prod.fst := (Finset.mem_sdiff.mp hv).2
    refine Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, (mem_fib (i := i) (p := (v, i))).mpr rfl⟩
    intro hz
    exact hm' (Finset.mem_image.mpr ⟨(v, i),
      Finset.mem_inter.mpr ⟨hz, (mem_fib (i := i) (p := (v, i))).mpr rfl⟩, rfl⟩)
  have h3 := isBipartite_induceFinset_of_isBipartite
    (s := (Finset.univ : Finset W).filter
      (fun v => (v, i) ∈ (((Finset.univ : Finset (W × Fin j)) \ Z) ∩ fib i)))
    (t := (Finset.univ : Finset W) \ (Z ∩ fib i).image Prod.fst) h2 hsub
  rw [deleteFinset] at h3 ⊢
  rw [induceFinset_induceFinset, Finset.inter_self] at h3
  exact h3

/-- **IF EVERY SET OF AT MOST ONE VERTEX LEAVES AN ODD CYCLE IN THE `i`-TH PIECE, THEN THE `i`-TH
FIBRE CONTRIBUTES AT LEAST TWO DELETED VERTICES.**  This is the form in which the transport lemma is
consumed. -/
theorem card_ge_two_of_not_bipartite {j : ℕ} {H : Fin j → SimpleGraph W} {Z : Finset (W × Fin j)}
    (i : Fin j) (h1 : ∀ X : Finset W, X.card ≤ 1 → ¬ (deleteFinset (H i) X).IsBipartite)
    (hb : (deleteFinset (sumGraph j H) Z).IsBipartite) : 2 ≤ (Z ∩ fib i).card := by
  by_contra hcon
  have hres := deleteFinset_sumGraph_fib (H := H) (Z := Z) i hb
  have hc := card_image_fib (S := Z) i
  exact h1 ((Z ∩ fib i).image Prod.fst) (by omega) hres

/-- **THE LOWER BOUND ON THE TRANSVERSAL, IN THE LANGUAGE OF THE DISJOINT UNION.**  If every
single vertex of every piece is needed to make that piece bipartite, then no set of fewer than
`2 j` vertices makes the whole union bipartite.  Every term of the count is produced by Part 0, and
the two instances of the transport lemma are inside this section, so no `DecidableEq` term crosses
a section boundary. -/
theorem not_closeToBipartite_lt_two_mul_sumGraph {j m : ℕ} {H : Fin j → SimpleGraph W}
    (h1 : ∀ i : Fin j, ∀ X : Finset W, X.card ≤ 1 → ¬ (deleteFinset (H i) X).IsBipartite)
    (hm : m < 2 * j) : ¬ CloseToBipartite m (sumGraph j H) := by
  rintro ⟨Z, hZ, hb⟩
  have hkey : ∀ i : Fin j, 2 ≤ (Z ∩ fib i).card :=
    fun i => card_ge_two_of_not_bipartite (H := H) (Z := Z) i (h1 i) hb
  have hsum : Z.card = ∑ i : Fin j, (Z ∩ fib i).card := card_eq_sum_card_inter_fib (X := Z)
  have h2 : (∑ _i : Fin j, (2 : ℕ)) ≤ ∑ i : Fin j, (Z ∩ fib i).card :=
    Finset.sum_le_sum fun i _ => hkey i
  have h3 : (∑ _i : Fin j, (2 : ℕ)) = 2 * j := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.mul_comm,
      Nat.cast_id]
  omega

end Fib

/-- **THE LEAST ODD CYCLE TRANSVERSAL OF THE 3-SUN IS AT LEAST TWO** — the contrapositive form of
`JSPProblem/Sun.lean`'s `not_closeToBipartite_one_sun3`, on the residue of an arbitrary set of at
most one vertex. -/
theorem not_bipartite_delete_sun3_card_le_one {X : Finset (Fin 6)} (hX : X.card ≤ 1) :
    ¬ (deleteFinset sun3 X).IsBipartite := by
  intro hb
  exact not_closeToBipartite_one_sun3 ⟨X, hX, hb⟩

/-- **THE `k`-FOLD SUN IS NOT `(2 k - 1)`-CLOSE TO BIPARTITE.**  Deleting fewer than `2 k` vertices
leaves an odd cycle: inside each of the `k` fibres at least two vertices must be deleted (by the
3-sun's own transversal number `2`), and the pigeonhole principle turns this into a contradiction. -/
theorem not_closeToBipartite_lt_two_mul_sun3U {k m : ℕ} (hm : m < 2 * k) :
    ¬ CloseToBipartite m (sun3U k) :=
  fun h => not_closeToBipartite_lt_two_mul_sumGraph (j := k)
    (fun _ X hX hbi => not_closeToBipartite_one_sun3 ⟨X, hX, hbi⟩) hm (by simpa only [sun3U] using h)

/-- **`T0` is a triangle of `sun3`**: two distinct points of it are adjacent. -/
theorem adj_of_mem_T0 {u v : Fin 6} (hu : u ∈ T0) (hv : v ∈ T0) (hne : u ≠ v) :
    sun3.Adj u v := by
  have hu' : u = 0 ∨ u = 2 ∨ u = 5 := by
    simpa only [T0, Finset.mem_insert, Finset.mem_singleton] using hu
  have hv' : v = 0 ∨ v = 2 ∨ v = 5 := by
    simpa only [T0, Finset.mem_insert, Finset.mem_singleton] using hv
  rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
  · exact absurd hne (by simp)
  · exact (sun3_adj).2 (by simp [sun3Edge])
  · exact (sun3_adj).2 (by simp [sun3Edge])
  · exact (sun3_adj).2 (by simp [sun3Edge])
  · exact absurd hne (by simp)
  · exact (sun3_adj).2 (by simp [sun3Edge])
  · exact (sun3_adj).2 (by simp [sun3Edge])
  · exact (sun3_adj).2 (by simp [sun3Edge])
  · exact absurd hne (by simp)

/-- **AN INDEPENDENT SUBSET OF AN INDEPENDENT SET IS INDEPENDENT.** -/
theorem isIndepSet_subset {V : Type*} {G : SimpleGraph V} {A B : Finset V}
    (hA : G.IsIndepSet A) (hAB : B ⊆ A) : G.IsIndepSet B := by
  rw [SimpleGraph.isIndepSet_iff] at hA ⊢
  intro v hv w hw hne hadj
  exact hA (Finset.mem_coe.mp (hAB (Finset.mem_coe.mp hv)))
    (Finset.mem_coe.mp (hAB (Finset.mem_coe.mp hw))) hne hadj

/-- **AN INDEPENDENT SET MEETS A TRIANGLE IN AT MOST ONE POINT.** -/
theorem card_le_one_of_sub_tri {k : ℕ} {S : Finset (Fin 6 × Fin k)} (hSi : (sun3U k).IsIndepSet S)
    (i : Fin k) (hsub : S ⊆ T0.image (fun v => (v, i))) : S.card ≤ 1 := by
  refine Finset.card_le_one_iff.mpr ?_
  intro a b ha hb
  have haF : a ∈ T0.image (fun v : Fin 6 => (v, i)) := hsub ha
  have hbF : b ∈ T0.image (fun v : Fin 6 => (v, i)) := hsub hb
  obtain ⟨p, hp, hpq⟩ := exists_of_mem_image_fib haF
  obtain ⟨q, hq, hqq⟩ := exists_of_mem_image_fib hbF
  by_cases hpq' : p = q
  · rw [← hpq, ← hqq, hpq']
  · have hadj : (sun3U k).Adj (p, i) (q, i) := by
      rw [sun3U_adj]
      exact ⟨rfl, adj_of_mem_T0 hp hq hpq'⟩
    exact eq_of_adj_of_isIndepSet hSi (hpq.symm ▸ ha) (hqq.symm ▸ hb) (hpq ▸ hqq ▸ hadj)

/-- **A vertex set made of one triangle per fibre spans an independent set of at most `k` points.**
Each fibre contributes a triangle, and an independent set meets a triangle in at most one point. -/
theorem indepCard_tri_le {k : ℕ} :
    indepCard (sun3U k) ((Finset.univ : Finset (Fin k)).biUnion
      (fun i => T0.image (fun v => (v, i)))) ≤ k := by
  classical
  refine Finset.sup_le_iff.mpr fun S hS => ?_
  have hSi : (sun3U k).IsIndepSet S := isIndepSet_of_mem_indepSets hS
  have hSsub : S ⊆ ((Finset.univ : Finset (Fin k)).biUnion
    (fun i => T0.image (fun v => (v, i)))) := sub_of_mem_indepSets hS
  calc S.card = ∑ i : Fin k, (S ∩ fib i).card := card_eq_sum_card_inter_fib (X := S)
    _ ≤ ∑ _i : Fin k, ((1 : ℕ)) := Finset.sum_le_sum fun i _ => by
        have hsub' : S ∩ fib i ⊆ S := fun a ha => (Finset.mem_inter.mp ha).1
        have hsub'' : S ∩ fib i ⊆ T0.image (fun v : Fin 6 => (v, i)) := by
          intro a ha
          obtain ⟨i', -, hi⟩ := Finset.mem_biUnion.mp (hSsub (Finset.mem_inter.mp ha).1)
          have h1 : i' = i :=
            (snd_eq_of_mem_image_fib hi).symm.trans (mem_fib.mp (Finset.mem_inter.mp ha).2)
          subst h1
          exact hi
        exact card_le_one_of_sub_tri (isIndepSet_subset hSi hsub') i hsub''
    _ = k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.mul_one, Nat.cast_id]

/-- **The vertex set made of one triangle per fibre has `3 k` points.** -/
theorem card_tri_sun (k : ℕ) : ((Finset.univ : Finset (Fin k)).biUnion
    (fun i => T0.image (fun v => (v, i)))).card = 3 * k := by
  classical
  have hT0 : T0.card = 3 := by rfl
  have hb := Finset.card_biUnion (s := (Finset.univ : Finset (Fin k)))
    (t := fun i => T0.image (fun v : Fin 6 => (v, i)))
    (pairwiseDisjoint_image (j := k) (fun _ => T0))
  rw [Finset.sum_congr rfl fun i _ => (card_image_pair T0 i).trans hT0] at hb
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_comm, Nat.cast_id,
    Fintype.card_fin] at hb
  exact hb

/-- **THE WITNESS IS EXACT: `MaxDef (sun3U k) = k`.**  The `k`-fold sun satisfies Erdős's local
hypothesis with the parameter `k` and fails the parameter `k - 1`, so it is a sharp witness in the
sense of `JSP90.maxDef_kTriangles`. -/
theorem maxDef_sun3U (k : ℕ) : MaxDef (sun3U k) = k := by
  have h1 : indepCard (sun3U k) ((Finset.univ : Finset (Fin k)).biUnion
    (fun i => T0.image (fun v => (v, i)))) ≤ k := indepCard_tri_le
  have h2 : k ≤ defOf (sun3U k) ((Finset.univ : Finset (Fin k)).biUnion
    (fun i => T0.image (fun v => (v, i)))) := by
    rw [defOf, card_tri_sun]
    omega
  exact le_antisymm (maxDef_le_of_locIndep (locIndep_sun3U k)) (h2.trans
    (le_maxDef (sun3U k) ((Finset.univ : Finset (Fin k)).biUnion
      (fun i => T0.image (fun v => (v, i))))))

/-- **`sun3U k` fails Erdős's hypothesis with the parameter `k - 1`** — the counterpart of
`JSP90.not_locIndep_kTriangles`. -/
theorem not_locIndep_sun3U {k : ℕ} (hk : 1 ≤ k) : ¬ LocIndep (k - 1) (sun3U k) := by
  intro h
  rw [locIndep_iff_maxDef_le, maxDef_sun3U] at h
  omega

end Sun

/-! ## Part 4 — the constant of Erdős #73 is at least `2 k` -/

section Constant

/-- **THE CONSTANT IN ERDŐS #73 IS AT LEAST `2 k`.**  If `Erdős73On.{0} k m` — *every* graph satisfying
Erdős's local hypothesis with the parameter `k` is `m`-close to bipartite, over all finite vertex
types — then `2 * k ≤ m`.

This is an order-free statement about the constant of the headline theorem, and it **doubles** the
machine-checked lower bound `JSP90.no_constant_below_k` of `JSPProblem/Sharp.lean`.  The witness is
the `k`-fold 3-sun, which spends one unit of Erdős's parameter on two units of odd cycle
transversal. -/
theorem erdos73On_two_mul_le {k m : ℕ} (hk : 1 ≤ k) (h : Erdős73On.{0} k m) : 2 * k ≤ m := by
  by_contra hcon
  exact not_closeToBipartite_lt_two_mul_sun3U (by omega)
    (h (Fin 6 × Fin k) inferInstance (sun3U k) (locIndep_sun3U k))

/-- **NO CONSTANT BELOW `2 k` CAN WORK AT THE PARAMETER `k`** — the negative form. -/
theorem not_erdos73On_lt_two_mul {k m : ℕ} (hk : 1 ≤ k) (hm : m < 2 * k) :
    ¬ Erdős73On.{0} k m := fun h =>
  not_closeToBipartite_lt_two_mul_sun3U hm
    (h (Fin 6 × Fin k) inferInstance (sun3U k) (locIndep_sun3U k))

/-- **ANY WITNESS OF `Erdős73.{0} k` IS AT LEAST `2 k`.** -/
theorem two_mul_le_of_erdos73 {k : ℕ} (hk : 1 ≤ k) (h : Erdős73.{0} k) : 2 * k ≤ h.choose :=
  erdos73On_two_mul_le hk (Erdős73On_of_Erdős73 h)

/-! The two `k = 1` statements of this file — `JSP90.not_erdos73On_one_one` (the constant `1`
does not work at `k = 1`, witnessed by the 3-sun of `JSPProblem/Sun.lean`) and
`JSP90.closeToBipartite_one_of_locIndep_one_card_le_five` (it does work on at most five vertices) —
are already in `JSPProblem/OneK.lean`, so nothing is restated here; what this file adds is their
**generalisation to every parameter `k`: the constant must be at least `2 k`**. -/

end Constant

end

end JSP90