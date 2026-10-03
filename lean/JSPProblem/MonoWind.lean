/-
# JSP-000090 — round 128: the **windmill refutation** of the *relative* max-cut hypothesis

Round 127 left the maximum-cut axis with the hypothesis

> `JSP90.MaxCutMonoLe c`: every graph of deficiency `≤ k` admits a *stable* cut whose mono set has
> at most `c` vertices,

together with the measured conjecture that a bound `card (MonoSet G A) ≤ phi (MaxDef G)` should
exist (`phi(1) = 4`, `phi(2) ≥ 7`, measured over all graphs on `≤ 8` vertices).  Round 128 refuted
the first statement (`JSP90.not_maxCutMonoLe` in `JSPProblem/CutFlip.lean`); this file refutes the
second, and it does so with the *optimal* transversal number.

## The witness

`JSP90.wfT t` is the **windmill with `t` triangles**: one hub and, for each `i : Fin t`, two leaves
`inl (i, 0)`, `inl (i, 1)` joined to each other and to the hub, with no edges between different
triangles.  The hub is what makes the example decisive:

* **`JSP90.closeToBipartite_one_wfT`** — deleting the hub leaves a matching, so the windmill `t` is
  `1`-close to bipartite for every `t`, and (see `JSPProblem/Petersen.lean` for the same value at
  odd girth `5`) its optimal odd cycle transversal number is `1`.
* The triangles all **share** the hub, so their deficiencies do not add: this is the family
  `MaxDef = 1` (round 89's `wf` is the case `t = 2`).
* **`JSP90.card_monoSet_ge_t_add_one'`** — yet **every** cut of the windmill `t` has a mono set of
  at least `t + 1` vertices, and `JSP90.card_monoSet_ge_t_add_one` shows the bound is attained when
  the hub is mono.  So the mono set of a cut — the only certificate the maximum-cut route can
  produce — is *unboundedly* worse than the optimum, while `MaxDef` stays `1`.

The combinatorial core (`JSP90.exists_mono_leaf_of_wfT`): in each triangle at least one of the two
leaves is mono for **every** cut, because a leaf is mono either through the hub (if it is on the
hub's side) or through its partner; the two cases are exhaustive.  If the hub itself is not mono,
then no leaf is on the hub's side (`JSP90.leaf_mem_monoSet_of_not_mem_hub`), so *both* leaves of
every triangle are mono and the mono set has `2 t` vertices.

## What this kills

Any statement of the form "for every `phi` there is a bound on the mono set of a cut in terms of
`MaxDef`" — including the conjecture recorded in round 127 — is refuted as soon as the windmill
satisfies `LocIndep 1`.  That last input is **`JSP90.locIndep_one_wfT`, proved below** (round
129), so the relative refutation is complete: the windmill is a family of `LocIndep 1` graphs with
optimal odd cycle transversal number `1` and cut certificates tending to infinity, and **no
function of `MaxDef` bounds the mono set of a cut**.

## Part 2 — the windmill satisfies Erdős's hypothesis with `k = 1`

`JSP90.locIndep_one_wfT` is a *counting* statement and no combinatorics is needed.  For a vertex
set `X` put `selOf X i` = the leaf of triangle `i` that lies in `X` (whichever of the two leaves
`X` meets; a triangle that meets `X` always contributes at least one leaf, and if only the far leaf
is in `X` that one is chosen).  Then

* `S = (univ.image (selOf X)) ∩ X` is **independent**: two elements of `S` are `selOf X i` and
  `selOf X i'`, and `selOf X` determines `i`, so adjacency of two distinct elements of `S` would
  force `i = i'` and hence equality (`JSP90.selOf_inj`);
* `|X ∩ leaves| ≤ 2 * |S|`: the map `inl (i, j) ↦ (selOf X i, j)` is injective on the leaves and
  lands in `S × Fin 2` (`JSP90.injOn_wfLeafMap`, `JSP90.fst_wfLeafMap_mem`);
* `|X| ≤ 1 + |X ∩ leaves|`, the hub being the only vertex that is not a leaf.

So `2 * |S| + 1 ≥ |X|` for every `X`, which is exactly `LocIndep 1`.

Nothing in this file is assumed: `JSP90.wfT` is a `SimpleGraph` with a proved `symm` and `loopless`,
and every counting statement is proved from the adjacency formula.
-/

import JSPProblem.CutFlip

namespace JSP90
open Finset Fintype Set Sum
noncomputable section

/-- The windmill `wfT t`: `t` triangles sharing a single hub. -/
def wfAdjT {t : ℕ} (a b : Sum (Fin t × Fin 2) Unit) : Prop :=
  match a, b with
  | Sum.inr _, Sum.inl _ => True
  | Sum.inl _, Sum.inr _ => True
  | Sum.inl (i, j), Sum.inl (i', j') => i = i' ∧ j ≠ j'
  | Sum.inr _, Sum.inr _ => False

def wfT (t : ℕ) : SimpleGraph (Sum (Fin t × Fin 2) Unit) where
  Adj v w := wfAdjT v w
  symm := ⟨fun a b h => by
    cases a with
    | inr e => cases b with
      | inr _ => exact h
      | inl _ => trivial
    | inl p => cases p with
      | mk i j => cases b with
        | inr _ => trivial
        | inl q => cases q with
          | mk i' j' => exact ⟨h.1.symm, fun hj => h.2 hj.symm⟩⟩
  loopless := ⟨fun a h => by
    cases a with
    | inr e => exact h
    | inl p => cases p with
      | mk i j => exact h.2 rfl⟩

@[simp] theorem adj_wfT_hub_leaf {t : ℕ} (i : Fin t) (j : Fin 2) :
    (wfT t).Adj (Sum.inr () : Sum (Fin t × Fin 2) Unit) (Sum.inl (i, j)) := trivial

@[simp] theorem adj_wfT_leaf_hub {t : ℕ} (i : Fin t) (j : Fin 2) :
    (wfT t).Adj (Sum.inl (i, j) : Sum (Fin t × Fin 2) Unit) (Sum.inr ()) := trivial

theorem adj_wfT_leaf_leaf {t : ℕ} (i i' : Fin t) (j j' : Fin 2) :
    (wfT t).Adj (Sum.inl (i, j) : Sum (Fin t × Fin 2) Unit) (Sum.inl (i', j')) ↔ i = i' ∧ j ≠ j' :=
  Iff.rfl

theorem not_adj_wfT_hub_hub (t : ℕ) :
    ¬ (wfT t).Adj (Sum.inr () : Sum (Fin t × Fin 2) Unit) (Sum.inr ()) := fun h => h

/-- **EVERY TRIANGLE OF THE WINDMILL CONTRIBUTES A MONOCHROMATIC LEAF TO EVERY CUT.**  A leaf is
mono either because it is on the same side of the cut as the hub, or -- if it is alone on its side
among the two leaves -- because of the edge to its partner. -/
theorem exists_mono_leaf_of_wfT (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit)) (i : Fin t) :
    Sum.inl (i, 0) ∈ MonoSet (wfT t) A ∨ Sum.inl (i, 1) ∈ MonoSet (wfT t) A := by
  classical
  have hadjxy : (wfT t).Adj (Sum.inl (i, 0) : Sum (Fin t × Fin 2) Unit) (Sum.inl (i, 1)) :=
    (adj_wfT_leaf_leaf i i 0 1).mpr ⟨rfl, by decide⟩
  by_cases hh : (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∈ A
  · by_cases hx0 : Sum.inl (i, 0) ∈ A
    · exact Or.inl (mem_monoSet.mpr ⟨Sum.inr (), adj_wfT_leaf_hub i 0, Or.inl ⟨hx0, hh⟩⟩)
    · by_cases hy0 : Sum.inl (i, 1) ∈ A
      · exact Or.inr (mem_monoSet.mpr ⟨Sum.inr (), adj_wfT_leaf_hub i 1, Or.inl ⟨hy0, hh⟩⟩)
      · exact Or.inl (mem_monoSet.mpr ⟨Sum.inl (i, 1), hadjxy, Or.inr ⟨hx0, hy0⟩⟩)
  · by_cases hx0 : Sum.inl (i, 0) ∈ A
    · by_cases hy0 : Sum.inl (i, 1) ∈ A
      · exact Or.inl (mem_monoSet.mpr ⟨Sum.inl (i, 1), hadjxy, Or.inl ⟨hx0, hy0⟩⟩)
      · exact Or.inr (mem_monoSet.mpr ⟨Sum.inr (), adj_wfT_leaf_hub i 1, Or.inr ⟨hy0, hh⟩⟩)
    · exact Or.inl (mem_monoSet.mpr ⟨Sum.inr (), adj_wfT_leaf_hub i 0, Or.inr ⟨hx0, hh⟩⟩)

/-- **THE HUB CHOOSES ONE MONO LEAF PER TRIANGLE, AND THEY ARE DISTINCT.** -/
noncomputable def monoLeaf (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit)) (i : Fin t) :
    Sum (Fin t × Fin 2) Unit :=
  if Sum.inl (i, 0) ∈ MonoSet (wfT t) A then Sum.inl (i, 0) else Sum.inl (i, 1)

theorem mem_monoLeaf (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit)) (i : Fin t) :
    monoLeaf t A i ∈ MonoSet (wfT t) A := by
  classical
  unfold monoLeaf
  split
  · exact ‹_›
  · exact (exists_mono_leaf_of_wfT t A i).resolve_left ‹_›

theorem monoLeaf_inj (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit)) :
    Function.Injective (monoLeaf t A) := by
  intro i i' h
  simp only [monoLeaf] at h
  split at h <;> split at h
  · exact (Prod.mk.inj (Sum.inl.inj h)).1
  · exact absurd (Prod.mk.inj (Sum.inl.inj h)).2 (by decide)
  · exact absurd (Prod.mk.inj (Sum.inl.inj h)).2 (by decide)
  · exact (Prod.mk.inj (Sum.inl.inj h)).1

/-- **THE MONO SET OF ANY CUT OF THE WINDMILL HAS AT LEAST `t` VERTICES** — one per triangle. -/
theorem card_monoSet_ge_t (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit)) :
    t ≤ (MonoSet (wfT t) A).card := by
  classical
  have hsub : (Finset.univ : Finset (Fin t)).image (monoLeaf t A) ⊆ MonoSet (wfT t) A := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact mem_monoLeaf t A i
  calc t = ((Finset.univ : Finset (Fin t)).image (monoLeaf t A)).card :=
        ((Finset.card_image_of_injective _ (monoLeaf_inj t A)).trans (Finset.card_fin _)).symm
    _ ≤ (MonoSet (wfT t) A).card := Finset.card_le_card hsub

/-- **NO LEAF IS THE HUB.** -/
theorem monoLeaf_ne_hub (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit)) (i : Fin t) :
    monoLeaf t A i ≠ (Sum.inr () : Sum (Fin t × Fin 2) Unit) := by
  simp only [monoLeaf]
  split <;> simp

/-- **IF THE HUB IS MONO, THE MONO SET HAS AT LEAST `t + 1` VERTICES.** -/
theorem card_monoSet_ge_t_add_one (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit))
    (hh : (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∈ MonoSet (wfT t) A) :
    t + 1 ≤ (MonoSet (wfT t) A).card := by
  classical
  have hsub : insert (Sum.inr ())
      ((Finset.univ : Finset (Fin t)).image (monoLeaf t A)) ⊆ MonoSet (wfT t) A := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hh
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact mem_monoLeaf t A i
  have hne : (Sum.inr () : Sum (Fin t × Fin 2) Unit)
      ∉ (Finset.univ : Finset (Fin t)).image (monoLeaf t A) := by
    intro hx
    obtain ⟨i, -, he⟩ := Finset.mem_image.mp hx
    exact (monoLeaf_ne_hub t A i) he
  have hcard : (insert (Sum.inr ()) ((Finset.univ : Finset (Fin t)).image (monoLeaf t A))).card
      = t + 1 := by
    have h2 := Finset.card_insert_of_notMem hne
    have h3 := Finset.card_image_of_injective (Finset.univ : Finset (Fin t)) (monoLeaf_inj t A)
    have hfin : (Finset.univ : Finset (Fin t)).card = t := Finset.card_fin _
    omega
  calc t + 1 = (insert (Sum.inr ()) ((Finset.univ : Finset (Fin t)).image (monoLeaf t A))).card :=
        hcard.symm
    _ ≤ (MonoSet (wfT t) A).card := Finset.card_le_card hsub

/-- **THE PARTNER OF A LEAF** — the other leaf of the same triangle. -/
def partner (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0

theorem partner_ne (j : Fin 2) : partner j ≠ j := by
  fin_cases j <;> simp [partner]

@[simp] theorem adj_wfT_partner {t : ℕ} (i : Fin t) (j : Fin 2) :
    (wfT t).Adj (Sum.inl (i, j) : Sum (Fin t × Fin 2) Unit) (Sum.inl (i, partner j)) :=
  (adj_wfT_leaf_leaf i i j (partner j)).mpr ⟨rfl, Ne.symm (partner_ne j)⟩

/-- **IF A LEAF IS ON THE OTHER SIDE OF THE CUT FROM THE HUB, THE HUB IS ON SIDE `A`.** -/
theorem mem_A_of_not_mem_hub_of_not_mem_leaf (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit))
    (hh : (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∉ MonoSet (wfT t) A) (i : Fin t) (k : Fin 2)
    (h : Sum.inl (i, k) ∉ A) : (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∈ A := by
  by_contra hn
  exact hh (mem_monoSet.mpr
    ⟨Sum.inl (i, k), adj_wfT_hub_leaf i k, Or.inr ⟨hn, h⟩⟩)

/-- **IF THE HUB IS NOT MONO, EVERY LEAF IS**: the hub has no same-side neighbour, so in each
triangle both leaves lie on the side opposite the hub, and each leaf has its partner there. -/
theorem leaf_mem_monoSet_of_not_mem_hub (t : ℕ) (A : Finset (Sum (Fin t × Fin 2) Unit))
    (hh : (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∉ MonoSet (wfT t) A) (i : Fin t) (j : Fin 2) :
    Sum.inl (i, j) ∈ MonoSet (wfT t) A := by
  have hA : Sum.inl (i, j) ∈ A ↔ Sum.inl (i, partner j) ∈ A := by
    constructor
    · intro hjA
      by_contra hpart
      have hhub := mem_A_of_not_mem_hub_of_not_mem_leaf t A hh i (partner j) hpart
      exact hh (mem_monoSet.mpr ⟨Sum.inl (i, j), adj_wfT_leaf_hub i j, Or.inl ⟨hhub, hjA⟩⟩)
    · intro hpart
      by_contra hx
      have hhub : ¬ (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∈ A := by
        intro hhub'
        exact hh (mem_monoSet.mpr
          ⟨Sum.inl (i, partner j), adj_wfT_leaf_hub i (partner j), Or.inl ⟨hhub', hpart⟩⟩)
      exact hh (mem_monoSet.mpr ⟨Sum.inl (i, j), adj_wfT_leaf_hub i j, Or.inr ⟨hhub, hx⟩⟩)
  refine mem_monoSet.mpr ⟨Sum.inl (i, partner j), adj_wfT_partner i j, ?_⟩
  by_cases hx : Sum.inl (i, j) ∈ A
  · exact Or.inl ⟨hx, hA.mp hx⟩
  · exact Or.inr ⟨hx, fun hp => hx (hA.mpr hp)⟩

/-- **THE MONO SET OF ANY CUT OF THE WINDMILL `t` HAS AT LEAST `t + 1` VERTICES.** -/
theorem card_monoSet_ge_t_add_one' (t : ℕ) (ht : 1 ≤ t) (A : Finset (Sum (Fin t × Fin 2) Unit)) :
    t + 1 ≤ (MonoSet (wfT t) A).card := by
  by_cases hh : (Sum.inr () : Sum (Fin t × Fin 2) Unit) ∈ MonoSet (wfT t) A
  · exact card_monoSet_ge_t_add_one t A hh
  · have hall : (Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).erase (Sum.inr ())
        ⊆ MonoSet (wfT t) A := by
      intro x hx
      cases x with
      | inl p => cases p with
        | mk i j => exact leaf_mem_monoSet_of_not_mem_hub t A hh i j
      | inr e => exact False.elim ((Finset.mem_erase.mp hx).1 rfl)
    have hcard : ((Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).erase (Sum.inr ())).card
        = 2 * t := by
      have h1 : ((Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).erase (Sum.inr ())).card + 1
          = (Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).card :=
        Finset.card_erase_add_one (Finset.mem_univ _)
      have h2 : (Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).card = 2 * t + 1 := by
        have h3 : Fintype.card (Sum (Fin t × Fin 2) Unit) = 2 * t + 1 := by
          simp
          omega
        exact (Finset.card_univ.trans h3)
      omega
    calc t + 1 ≤ 2 * t := by omega
      _ = ((Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).erase (Sum.inr ())).card :=
        hcard.symm
      _ ≤ (MonoSet (wfT t) A).card := Finset.card_le_card hall

/-- **DELETING THE HUB LEAVES A MATCHING, WHICH IS BIPARTITE**: the windmill `t` is
`1`-close to bipartite for every `t`. -/
theorem closeToBipartite_one_wfT (t : ℕ) : CloseToBipartite 1 (wfT t) := by
  refine ⟨{Sum.inr ()}, by simp, ?_⟩
  refine ⟨SimpleGraph.Coloring.mk (fun v => match v with
    | Sum.inl (i, j) => j
    | Sum.inr _ => (0 : Fin 2)) ?_⟩
  intro v w hv
  simp only [deleteFinset_adj] at hv
  rcases hv with ⟨hv1, hv2, hadj⟩
  by_cases hv' : v = Sum.inr ()
  · subst hv'; simp at hv1
  · by_cases hw' : w = Sum.inr ()
    · subst hw'; simp at hv2
    · cases v with
      | inl p => cases p with
        | mk i j => cases w with
          | inl q => cases q with
            | mk i' j' =>
              simp only [adj_wfT_leaf_leaf] at hadj
              simp only [adj_wfT_leaf_leaf]
              exact fun h => hadj.2 h
          | inr e => simp at hw'
      | inr e => simp at hv'
end

/-! ### Part 2 — the windmill satisfies `LocIndep 1`, and the relative max-cut hypothesis dies -/

/-- **The hub** of the windmill `wfT t`. -/
def wfHub (t : ℕ) : Sum (Fin t × Fin 2) Unit := Sum.inr ()

/-- **The leaves** of the windmill `wfT t`: all vertices but the hub. -/
noncomputable def wfLeaves (t : ℕ) : Finset (Sum (Fin t × Fin 2) Unit) :=
  (Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).erase (wfHub t)

@[simp] theorem mem_wfLeaves {t : ℕ} {v : Sum (Fin t × Fin 2) Unit} :
    v ∈ wfLeaves t ↔ ∃ p : Fin t × Fin 2, v = Sum.inl p := by
  unfold wfLeaves
  rw [Finset.mem_erase]
  constructor
  · intro hv
    by_contra hcon
    cases v with
    | inl p => exact hcon ⟨p, rfl⟩
    | inr e => exact hv.1 rfl
  · rintro ⟨p, rfl⟩
    constructor
    · show Sum.inl p ≠ Sum.inr ()
      exact fun h => Sum.inl_ne_inr h
    · exact Finset.mem_univ _

/-- **THE WINDMILL HAS `2 t` LEAVES.** -/
theorem card_wfLeaves (t : ℕ) : (wfLeaves t).card = 2 * t := by
  have h : (wfLeaves t).card + 1 = (Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).card :=
    Finset.card_erase_add_one (Finset.mem_univ _)
  have h2 : (Finset.univ : Finset (Sum (Fin t × Fin 2) Unit)).card = 2 * t + 1 := by
    have h3 : Fintype.card (Sum (Fin t × Fin 2) Unit) = 2 * t + 1 := by
      simp
      omega
    exact Finset.card_univ.trans h3
  omega

/-- **THE LEAF OF TRIANGLE `i` CHOSEN BY `X`**: if `X` meets triangle `i`, this is a leaf of `i`
lying in `X`; it is the first leaf of `i` otherwise. -/
noncomputable def selOf {t : ℕ} (X : Finset (Sum (Fin t × Fin 2) Unit)) (i : Fin t) :
    Sum (Fin t × Fin 2) Unit :=
  if Sum.inl (i, 0) ∈ X then Sum.inl (i, 0) else Sum.inl (i, 1)

/-- **A TRIANGLE MEETING `X` HAS A LEAF IN `X`, AND IT IS THE ONE `selOf` RETURNS.** -/
theorem selOf_mem_of_mem_leaf {t : ℕ} {X : Finset (Sum (Fin t × Fin 2) Unit)} {i : Fin t}
    (h : ∃ j : Fin 2, Sum.inl (i, j) ∈ X) : selOf X i ∈ X := by
  by_cases h0 : Sum.inl (i, 0) ∈ X
  · simp [selOf, h0]
  · simp only [selOf, if_neg h0]
    obtain ⟨j, hj⟩ := h
    by_cases hj0 : j = 0
    · rw [hj0] at hj; exact (h0 hj).elim
    · have hj1 : j = 1 := by omega
      rw [hj1] at hj; exact hj

theorem exists_fin2_selOf {t : ℕ} {X : Finset (Sum (Fin t × Fin 2) Unit)} (i : Fin t) :
    ∃ j : Fin 2, selOf X i = Sum.inl (i, j) := by
  by_cases h0 : Sum.inl (i, 0) ∈ X
  · exact ⟨0, by simp [selOf, h0]⟩
  · exact ⟨1, by simp [selOf, h0]⟩

/-- **THE CHOSEN LEAF DETERMINES THE TRIANGLE.** -/
theorem selOf_inj {t : ℕ} {X : Finset (Sum (Fin t × Fin 2) Unit)} {i i' : Fin t}
    (h : selOf X i = selOf X i') : i = i' := by
  obtain ⟨j, hj⟩ := exists_fin2_selOf (X := X) i
  obtain ⟨j', hj'⟩ := exists_fin2_selOf (X := X) i'
  rw [hj, hj'] at h
  exact (Prod.mk.inj (Sum.inl.inj h)).1

/-- **The codomain of `wfLeafMap`**: a chosen leaf together with a label, or the marker
`inr ()` standing for the hub. -/
abbrev WfLeafPair (t : ℕ) : Type _ := ((Sum (Fin t × Fin 2) Unit) × Fin 2) ⊕ Unit

/-- **THE CHOSEN SET**: the chosen leaf of every triangle that meets `X`. -/
noncomputable def WfChosen (t : ℕ) (X : Finset (Sum (Fin t × Fin 2) Unit)) :
    Finset (Sum (Fin t × Fin 2) Unit) :=
  (Finset.univ : Finset (Fin t)).image (selOf X) ∩ X

/-- **THE MAP FROM A CHOSEN LEAF AND ITS LABEL TO THE CODE**, used to count the leaves of a vertex
set. -/
noncomputable def wfLabelOf {t : ℕ} (p : (Sum (Fin t × Fin 2) Unit) × Fin 2) : WfLeafPair t :=
  Sum.inl p

theorem wfLabelOf_injective {t : ℕ} : Function.Injective (wfLabelOf (t := t)) := by
  intro a b h
  simp only [wfLabelOf] at h
  injection h

/-- **THE CODED CHOSEN SET**: the codes of the pairs (chosen leaf, label); it has twice the size of
the chosen set. -/
noncomputable def WfChosenCode (t : ℕ) (X : Finset (Sum (Fin t × Fin 2) Unit)) :
    Finset (WfLeafPair t) :=
  Finset.product (WfChosen t X) (Finset.univ : Finset (Fin 2)) |>.image wfLabelOf

theorem card_WfChosenCode (t : ℕ) (X : Finset (Sum (Fin t × Fin 2) Unit)) :
    (WfChosenCode t X).card = 2 * (WfChosen t X).card := by
  rw [WfChosenCode, Finset.card_image_of_injective _ wfLabelOf_injective]
  rw [show ((WfChosen t X).product (Finset.univ : Finset (Fin 2))) = WfChosen t X
      ×ˢ (Finset.univ : Finset (Fin 2)) from rfl, Finset.card_product, Finset.card_fin _]
  omega

/-- **THE MAP `v ↦ (chosen leaf of `v`'s triangle, label of `v`)**; it is a total injection,
the hub being sent to the last summand. -/
noncomputable def wfLeafMap {t : ℕ} (X : Finset (Sum (Fin t × Fin 2) Unit))
    (v : Sum (Fin t × Fin 2) Unit) : WfLeafPair t :=
  match v with
  | Sum.inl (i, j) => wfLabelOf (selOf X i, j)
  | Sum.inr _ => Sum.inr ()

theorem wfLeafMap_inj {t : ℕ} (X : Finset (Sum (Fin t × Fin 2) Unit)) :
    Function.Injective (wfLeafMap X) := by
  classical
  intro a b h
  cases a with
  | inl p => cases p with
    | mk i j =>
      cases b with
      | inl q => cases q with
        | mk i' j' =>
          simp only [wfLeafMap, wfLabelOf] at h
          obtain ⟨hsel, hlab⟩ := Prod.mk.inj (Sum.inl.inj h)
          obtain hii : i = i' := selOf_inj hsel
          subst hii
          subst hlab
          rfl
      | inr e =>
        simp only [wfLeafMap, wfLabelOf] at h
        exact (Sum.inl_ne_inr h).elim
  | inr e =>
    cases b with
    | inl q => cases q with
      | mk i' j' =>
        simp only [wfLeafMap, wfLabelOf] at h
        exact (Sum.inl_ne_inr h.symm).elim
    | inr e => rfl

/-- **A LEAF IN `X` IS CODED BY THE CHOSEN LEAF OF ITS TRIANGLE AND ITS OWN LABEL.** -/
theorem mem_wfLeafMap_of_mem {t : ℕ} {X : Finset (Sum (Fin t × Fin 2) Unit)}
    {v : Sum (Fin t × Fin 2) Unit} (hv : v ∈ X ∩ wfLeaves t) :
    wfLeafMap X v ∈ WfChosenCode t X := by
  obtain ⟨hx, hleaf⟩ := Finset.mem_inter.mp hv
  obtain ⟨p, hp⟩ := mem_wfLeaves.mp hleaf
  subst hp
  exact Finset.mem_image.mpr
    ⟨(selOf X p.1, p.2), Finset.mem_product.mpr ⟨Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩,
        selOf_mem_of_mem_leaf ⟨p.2, hx⟩⟩, Finset.mem_univ _⟩, rfl⟩

/-- **THE LEAVES OF `X` ARE COUNTED BY TWICE THE CHOSEN SET.** -/
theorem card_inter_wfLeaves_le_two_mul_card_inter_wfChosen {t : ℕ}
    (X : Finset (Sum (Fin t × Fin 2) Unit)) :
    (X ∩ wfLeaves t).card ≤ 2 * (WfChosen t X).card := by
  have hsub : (X ∩ wfLeaves t).image (wfLeafMap X) ⊆ WfChosenCode t X := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact mem_wfLeafMap_of_mem hv
  calc (X ∩ wfLeaves t).card = ((X ∩ wfLeaves t).image (wfLeafMap X)).card :=
      (Finset.card_image_of_injective (X ∩ wfLeaves t) (wfLeafMap_inj X)).symm
    _ ≤ (WfChosenCode t X).card := Finset.card_le_card hsub
    _ = 2 * (WfChosen t X).card := card_WfChosenCode t X

/-- **A VERTEX SET IS ITS LEAVES PLUS AT MOST THE HUB.** -/
theorem card_le_card_inter_wfLeaves_add_one {t : ℕ}
    (X : Finset (Sum (Fin t × Fin 2) Unit)) : X.card ≤ (X ∩ wfLeaves t).card + 1 := by
  have hsub : X ⊆ (X ∩ wfLeaves t) ∪ {wfHub t} := by
    intro x hx
    by_cases hleaf : x ∈ wfLeaves t
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hleaf⟩)
    · refine Finset.mem_union_right _ (Finset.mem_singleton.mpr ?_)
      cases x with
      | inl q => exact absurd (mem_wfLeaves.mpr ⟨q, rfl⟩) hleaf
      | inr e => rfl
  calc X.card ≤ ((X ∩ wfLeaves t) ∪ {wfHub t}).card := Finset.card_le_card hsub
    _ ≤ (X ∩ wfLeaves t).card + 1 := Finset.card_union_le _ _

/-- **THE WINDMILL `t` SATISFIES ERDŐS'S LOCAL HYPOTHESIS WITH `k = 1`, FOR EVERY `t`.**

This is the counting lemma recorded as the one open input of round 128.  Combined with
`JSP90.closeToBipartite_one_wfT` (the windmill is `1`-close to bipartite for every `t`) and
`JSP90.card_monoSet_ge_t_add_one'` (every cut of it has a mono set of at least `t + 1` vertices)
it **completes the refutation of the relative maximum-cut hypothesis**: see
`JSP90.not_exists_monoSet_le_of_maxDef_one`. -/
theorem locIndep_one_wfT (t : ℕ) : LocIndep 1 (wfT t) := by
  intro X
  refine ⟨WfChosen t X, Finset.inter_subset_right, ?_, ?_⟩
  · refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hw).1
    obtain ⟨j, hj⟩ := exists_fin2_selOf (X := X) i
    obtain ⟨j', hj'⟩ := exists_fin2_selOf (X := X) i'
    rw [hj, hj'] at hadj
    simp only [wfT, wfAdjT] at hadj
    obtain ⟨hii, hjj⟩ := hadj
    have hvv : selOf X i = selOf X i' := by rw [hii]
    have hp : (Sum.inl (i, j) : Sum (Fin t × Fin 2) Unit) = Sum.inl (i', j') :=
      hj.symm.trans (hvv.trans hj')
    have hprod : (i, j) = (i', j') := Sum.inl.inj (β := Unit) hp
    exact hjj (Prod.mk.inj hprod).2
  · have h1 := card_inter_wfLeaves_le_two_mul_card_inter_wfChosen X
    have h2 := card_le_card_inter_wfLeaves_add_one X
    omega

/-- **The two leaves of triangle `0`** of the windmill `wfT t`. -/
def WfLeaves0 (t : ℕ) [NeZero t] : Finset (Sum (Fin t × Fin 2) Unit) :=
  insert (Sum.inl (⟨0, 0⟩ : Fin t × Fin 2)) ({Sum.inl (⟨0, 1⟩ : Fin t × Fin 2)} :
    Finset (Sum (Fin t × Fin 2) Unit))

/-- **THE HUB IS ADJACENT TO EVERY LEAF OF THE FIRST TRIANGLE.** -/
theorem adj_hub_of_mem_leaves0 {t : ℕ} [NeZero t] {v : Sum (Fin t × Fin 2) Unit}
    (hv : v ∈ WfLeaves0 t) : (wfT t).Adj (Sum.inr ()) v := by
  simp only [WfLeaves0] at hv
  rcases Finset.mem_insert.mp hv with hv | hv
  · rw [hv]; exact adj_wfT_hub_leaf (t := t) 0 0
  · rw [Finset.mem_singleton.mp hv]; exact adj_wfT_hub_leaf (t := t) 0 1

/-- **TWO DISTINCT LEAVES OF THE FIRST TRIANGLE ARE ADJACENT.** -/
theorem adj_leaves0 {t : ℕ} [NeZero t] {v w : Sum (Fin t × Fin 2) Unit}
    (hv : v ∈ WfLeaves0 t) (hw : w ∈ WfLeaves0 t) (hne : v ≠ w) :
    (wfT t).Adj v w := by
  simp only [WfLeaves0] at hv hw
  rcases Finset.mem_insert.mp hv with hv | hv
  · rcases Finset.mem_insert.mp hw with hw | hw
    · exact absurd (hv.trans hw.symm) hne
    · rw [hv, Finset.mem_singleton.mp hw]
      exact (adj_wfT_leaf_leaf (t := t) 0 0 0 1).2 ⟨rfl, by decide⟩
  · rcases Finset.mem_insert.mp hw with hw | hw
    · rw [hw, Finset.mem_singleton.mp hv]
      exact (adj_wfT_leaf_leaf (t := t) 0 0 1 0).2 ⟨rfl, by decide⟩
    · exact absurd
        ((Finset.mem_singleton.mp hv).trans (Finset.mem_singleton.mp hw).symm) hne

/-- **ONE TRIANGLE OF THE WINDMILL `t`**: the hub together with the two leaves of triangle `0`. -/
def wfTri0 (t : ℕ) [NeZero t] : Finset (Sum (Fin t × Fin 2) Unit) :=
  insert (Sum.inr ()) (WfLeaves0 t)

theorem card_wfTri0 (t : ℕ) [NeZero t] : (wfTri0 t).card = 3 := by
  rw [wfTri0, WfLeaves0, Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

/-- **ONE TRIANGLE OF THE WINDMILL IS A CLIQUE**, so it has deficiency `1`. -/
theorem isClique_wfTri0 (t : ℕ) [NeZero t] : (wfT t).IsClique (↑(wfTri0 t) : Set _) := by
  intro x hx y hy hxy
  have hx' : x ∈ wfTri0 t := hx
  have hy' : y ∈ wfTri0 t := hy
  rw [wfTri0] at hx' hy'
  rcases Finset.mem_insert.mp hx' with hx | hx
  · rcases Finset.mem_insert.mp hy' with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx]; exact adj_hub_of_mem_leaves0 (t := t) hy
  · rcases Finset.mem_insert.mp hy' with hy | hy
    · rw [hy]; exact (adj_hub_of_mem_leaves0 (t := t) hx).symm
    · exact adj_leaves0 (t := t) hx hy hxy

/-- **THE MAXIMUM DEFICIENCY OF THE WINDMILL `t` IS EXACTLY `1`** (`t ≥ 1`): its triangles all share
the hub, so their deficiencies do not add, while each triangle has deficiency `1`. -/
theorem maxDef_one_wfT (t : ℕ) [NeZero t] : MaxDef (wfT t) = 1 := by
  have htri : defOf (wfT t) (wfTri0 t) = 1 := defOf_eq_one_of_clique_card_three
    ⟨Sum.inr (), Finset.mem_insert_self _ _⟩ (isClique_wfTri0 t) (card_wfTri0 t)
  have h1 : MaxDef (wfT t) ≤ 1 := maxDef_le_of_locIndep (locIndep_one_wfT t)
  have h2 : 1 ≤ MaxDef (wfT t) := by
    have hle := le_maxDef (wfT t) (wfTri0 t)
    rw [htri] at hle
    omega
  omega

/-- **NO FUNCTION OF THE DEFICIENCY BOUNDS THE MONO SET OF A CUT.**

This is the final form of the refutation started in round 127 and completed here: there is **no**
`phi` such that every cut `A` of every graph with `MaxDef G ≤ 1` satisfies
`card (MonoSet G A) ≤ phi 1`.  The witness is the windmill `t := phi 1 + 1`, which satisfies
`LocIndep 1`, has maximum deficiency `1` and optimal odd cycle transversal number `1`, and whose
every cut has a mono set of at least `t + 1 = phi 1 + 2` vertices. -/
theorem not_exists_monoSet_le_of_maxDef_one {phi : ℕ → ℕ}
    (hphi : ∀ (W : Type 0) [Fintype W] (G : SimpleGraph W) (A : Finset W),
      LocIndep 1 G → MaxDef G ≤ 1 → (MonoSet G A).card ≤ phi 1) : False := by
  have ht : 1 ≤ phi 1 + 1 := by omega
  have h := hphi (Sum (Fin (phi 1 + 1) × Fin 2) Unit) (wfT (phi 1 + 1))
    (Finset.univ : Finset (Sum (Fin (phi 1 + 1) × Fin 2) Unit))
    (locIndep_one_wfT _) (by rw [maxDef_one_wfT _])
  have h2 := card_monoSet_ge_t_add_one' (phi 1 + 1) ht (Finset.univ)
  omega
/-- **THERE IS NO CUT CERTIFICATE AT ALL — NOT EVEN A FUNCTION OF THE LOCAL PARAMETER `k`.**

The final form of the maximum-cut certificate, and the sharpest negative statement the windmill
gives: for every function `phi` and every `k ≥ 1` there is a `LocIndep k` graph `G` and a cut `A` of
`G` with `(MonoSet G A).card > phi k` — although `G` is `1`-close to bipartite.  In other words, the
monochromatic set of a cut can be arbitrarily large while the *optimum* (a vertex of the hub) has
size `1`.  The witness is the windmill `t := phi k + 1`. -/
theorem not_exists_monoSet_le_of_locIndep {phi : ℕ → ℕ}
    (hphi : ∀ k, ∀ (W : Type 0) [Fintype W] (G : SimpleGraph W) (A : Finset W),
      LocIndep k G → (MonoSet G A).card ≤ phi k) : False := by
  have ht : 1 ≤ phi 1 + 1 := by omega
  have h := hphi 1 (Sum (Fin (phi 1 + 1) × Fin 2) Unit) (wfT (phi 1 + 1))
    (Finset.univ : Finset (Sum (Fin (phi 1 + 1) × Fin 2) Unit))
    (LocIndep.mono_k (locIndep_one_wfT _) (by omega))
  have h2 := card_monoSet_ge_t_add_one' (phi 1 + 1) ht (Finset.univ)
  omega

/-- **THE SAME, IN THE SHAPE OF THE HEADLINE STATEMENT**: for every `k ≥ 1` and every `m` there is a
`LocIndep k` graph that is `1`-close to bipartite and has a cut whose mono set has more than `m`
vertices.  So the maximum-cut route to Erdős #73 cannot produce **any** bound at all, in `k` or in
any function of `k`, while the optimum of the same family stays at `1`. -/
theorem exists_monoSet_ge_of_locIndep_of_closeToBipartite_one {k m : ℕ} (hk : 1 ≤ k) :
    ∃ (W : Type 0) (_ : Fintype W) (G : SimpleGraph W) (A : Finset W),
      LocIndep k G ∧ CloseToBipartite 1 G ∧ m < (MonoSet G A).card := by
  refine ⟨Sum (Fin (m + 1) × Fin 2) Unit, inferInstance, wfT (m + 1), Finset.univ,
    LocIndep.mono_k (locIndep_one_wfT _) hk, closeToBipartite_one_wfT _, ?_⟩
  have h2 := card_monoSet_ge_t_add_one' (m + 1) (by omega) (Finset.univ)
  omega

end JSP90
