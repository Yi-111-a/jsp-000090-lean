/-
# JSP-000090 — Erdős Problem #73 (Reed, *Mangoes and Blueberries*)

**Catalog record** (awards catalog, JSP-000090, status *Solved*, Lean proof *No*):

> *If local subgraphs have large independent sets, must the whole graph be close to
> bipartite after few modifications?*
>
> Mathematical area: Graph theory.  Date proposed: no later than 1982.
> Publication: `[Re99]` B. Reed, *Mangoes and Blueberries*, Combinatorica 19 (1999) 267–296.

## The precise mathematical statement

Erdős Problems #73 (`https://www.erdosproblems.com/73`) states:

> Let `k ≥ 0`.  Let `G` be a graph such that every subgraph `H` contains an independent set of
> size `≥ (n - k) / 2`, where `n` is the number of vertices of `H`.  Must `G` be the union of a
> bipartite graph and `O_k(1)` many vertices?

Reed proved this in 1999.  The `O_k(1)` of the question is the content of the theorem: for each
fixed `k` there is a constant `f(k)` bounding how many vertices must be removed before the
remainder is bipartite.

## This file

Two predicates, the induced subgraph operation, and the target statement `Erdős73`.

* `LocIndep k G` — Erdős's local hypothesis: every vertex set `X ⊆ V` carries an independent set
  `S ⊆ X` of size `2 * |S| + k ≥ |X|`, i.e. `|S| ≥ (|X| - k) / 2`.  Phrasing the bound in ℕ
  (`2 * |S| + k ≥ |X|`) keeps the whole development in ℕ and avoids the rounding ambiguity of the
  rational `(n - k) / 2`.

  Checking induced subgraphs `G[X]` rather than arbitrary subgraphs is equivalent to the original
  wording: if `H ≤ G` has vertex set `X` then every independent set of `H` is one of `G[X]`, and
  `α(H) ≤ α(G[X])`.

* `induceFinset G s` — the graph induced by a vertex set `s` of `G`, on the same vertex type, and
  `deleteFinset G X` — the graph left after deleting the vertices of `X`.

* `CloseToBipartite m G` — the conclusion: **deleting at most `m` vertices leaves a bipartite
  graph**, i.e. `G` is the union of a bipartite graph and `O_k(1)` many vertices.

  **Correction (round 34).**  This predicate used to be

  ```lean
  ∃ X : Finset V, X.card ≤ m ∧ ∃ s t : Set V, G.IsBipartiteWith s t ∧ (Set.univ \ (s ∪ t)) ⊆ (X : Set V)
  ```

  i.e. a bipartition `s, t` of the **whole** graph `G`, with the leftover vertices charged to `X`.
  That reading is *degenerate*: `G.IsBipartiteWith s t` forces every edge of `G` to join `s` to `t`,
  so the vertices of `V \ (s ∪ t)` are **isolated in `G`**, and the predicate reduces to "`G` is
  bipartite together with at most `m` isolated vertices".  Under it the catalog statement was
  **false already for `k = 1`**: the complete graph `K_3 = completeGraph (Fin 3)` satisfies
  `LocIndep 1` (`JSP90.completeGraph_locIndep`), so `Erdős73 1` would have been a false statement
  and no proof could ever exist.  The machine-checked record of that failure is
  `JSP90.rejected_reading_fails` in `JSPProblem/Transversal.lean`; the definition used here is the
  one the catalog question asks for, and it makes the `k = 1` sharp example
  `JSP90.closeToBipartite_completeGraph_three` provable.

* `Erdős73 k` — the full statement, quantifying `m` and ranging over all finite vertex types.

`JSPProblem/Reed.lean` proves the structural lemmas that are currently within reach; the
unproved core of the theorem is recorded in `JSPProblem.lean`.
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.SDiff

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

/-- **The graph induced by a vertex set `s` of `G`**, on the same vertex type `V`: two vertices of
`s` are adjacent exactly when they are adjacent in `G`.

Mathlib at the pinned revision `5ed29652` only offers `SimpleGraph.induce`, which lives on the
*subtype* of `s`; keeping the vertex type equal to `V` is what makes the `Finset` bookkeeping of
the rest of this development work. -/
def induceFinset (G : SimpleGraph V) (s : Finset V) : SimpleGraph V where
  Adj v w := v ∈ s ∧ w ∈ s ∧ G.Adj v w
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, G.adj_symm h.2.2⟩⟩
  loopless := ⟨fun v h => G.irrefl h.2.2⟩

@[simp] theorem induce_adj {G : SimpleGraph V} {s : Finset V} {v w : V} :
    (induceFinset G s).Adj v w ↔ v ∈ s ∧ w ∈ s ∧ G.Adj v w := Iff.rfl

local instance : DecidableEq V := Classical.decEq V

/-- **The graph left after deleting the vertices of `X`.**  This is the object the conclusion of
Erdős #73 talks about: "deleting at most `m` vertices leaves a bipartite graph". -/
def deleteFinset (G : SimpleGraph V) (X : Finset V) : SimpleGraph V :=
  induceFinset G (Finset.univ \ X)

@[simp] theorem deleteFinset_adj {G : SimpleGraph V} {X : Finset V} {v w : V} :
    (deleteFinset G X).Adj v w ↔ v ∉ X ∧ w ∉ X ∧ G.Adj v w := by
  rw [deleteFinset, induce_adj]
  simp

theorem deleteFinset_empty (G : SimpleGraph V) : deleteFinset G (∅ : Finset V) = G := by
  ext v w
  simp [deleteFinset_adj]

theorem isBipartite_delete {G : SimpleGraph V} {X : Finset V} (h : G.IsBipartite) :
    (deleteFinset G X).IsBipartite := by
  obtain ⟨d, hd⟩ := h
  exact ⟨SimpleGraph.Coloring.mk d (fun hadj => hd hadj.2.2)⟩

/-- **Erdős's local hypothesis (JSP-000090).**
`LocIndep k G` says that every vertex set `X ⊆ V` of `G` induces a graph with an independent set
of size at least `(|X| - k) / 2`, i.e. an independent set `S ⊆ X` with `2 * |S| + k ≥ |X|`.

The condition is automatically satisfied by every `H ≤ G` with vertex set `X` whenever it holds
for `G[X]`, so this captures "every subgraph `H` of `G` has an independent set of size at least
`(|V(H)| - k) / 2`". -/
def LocIndep (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ X : Finset V, ∃ S : Finset V, S ⊆ X ∧ G.IsIndepSet S ∧ 2 * S.card + k ≥ X.card

/-- **`CloseToBipartite m G`** says that `G` is *close to bipartite*: **deleting at most `m` vertices
leaves a bipartite graph**, i.e. `G` is the union of a bipartite graph and at most `m` vertices.

This is the formal reading of the catalog question "must the whole graph be close to bipartite
after few modifications", and of Erdős's "the union of a bipartite graph and `O_k(1)` many
vertices".  See the correction note in the file header. -/
def CloseToBipartite (m : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, X.card ≤ m ∧ (deleteFinset G X).IsBipartite

universe u

/-- The statement of JSP-000090 with an explicit constant `m`, ranging over all finite vertex
types in the universe `u`. -/
def Erdős73On (k m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → CloseToBipartite m G

/-- **JSP-000090 = Erdős Problem #73 (Reed 1999), the full statement.**

For every local-parameter `k` there is a constant `m` such that every finite graph satisfying
Erdős's local hypothesis `LocIndep k` is the union of a bipartite graph and at most `m` vertices.

This is a `def` rather than a `theorem`: it is the precise, machine-checked target of the
formalization, and it is *not* proved here.  See `JSPProblem.lean` for the list of results proved
in this development and for the exact statement that is still missing. -/
def Erdős73 (k : ℕ) : Prop := ∃ m : ℕ, Erdős73On.{u} k m

/-- A witness `m` supplied by `Erdős73 k` works on every finite vertex type. -/
theorem Erdős73On_of_Erdős73 {k : ℕ} (h : Erdős73.{u} k) : Erdős73On.{u} k h.choose :=
  h.choose_spec

end

end JSP90
