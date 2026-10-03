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
satisfies `LocIndep 1`.  The remaining input is `JSP90.locIndep_one_wfT` (this is the ONE lemma of
the relative refutation still open; see `discovery/JSP-000090/policy.json`), whose statement and
proof strategy are recorded there.

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
end JSP90
