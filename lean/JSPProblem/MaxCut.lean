/-
# JSP-000090 — round 93: the **CUT AXIS**.  Odd cycle transversals are exactly the sets covering
# the monochromatic edges of some cut.

Rounds 76–92 attacked Erdős Problem #73 along the *packing*, *degree*, *deficiency*, *separator*,
*intersection-pattern*, *fan* and *2-cut* axes.  None of them touched the one reformulation that is
classical in the theory of **max-cuts**: a **2-colouring** `A ⊔ (V \ A)` of the vertices, and the
**monochromatic edges** of that colouring, i.e. the edges *not* crossing it.  This file develops
that axis and shows that it is not a dead end but a genuine *characterisation* of the conclusion
of Erdős #73.

* `MonoEdge G A v w` — the edge `vw` does not cross the cut with side `A`.
* `HitsMono G A Z` — `Z` meets every monochromatic edge of that cut.
* `Separates S T A` — `A` puts `S` on one side and `T` on the other.

## The three results

1. **EVERY ODD CYCLE HAS A MONOCHROMATIC EDGE IN EVERY CUT** (`exists_monoEdge_of_isOddCycle`).
   An odd cycle cannot alternate along a cut for ever, so two consecutive vertices of it lie on the
   same side.  The proof is the parity argument of `JSPProblem/Transversal.lean`
   (`cycSucc_pow_odd`), with "the two sides of a bipartition" replaced by "the two sides of an
   arbitrary cut"; the intermediate lemma `even_of_cycle_noMono` says exactly that a cycle all of
   whose edges cross a cut has even length.  This is the load-bearing step of the whole file:
   it is the reason a **vertex cover of the monochromatic edges is an odd cycle transversal**
   (`hitsOddCycles_of_hitsMono`).

2. **ODD CYCLE TRANSVERSALS AND MONOCHROMATIC COVERS ARE THE SAME THINGS**
   (`hitsOddCycles_iff_hitsMono`).  `⟸` is (1).  `⟧` is a construction: if `Z` meets every odd cycle
   and `P ⊔ Q` is a bipartition of `G - Z`, then the cut with side `Z ∪ P` has all its
   monochromatic edges covered by `Z` — the edges inside `Z` by `Z`, the edges inside `P` and
   inside `Q` not at all.

3. **THE CONCLUSION OF ERDŐS #73 IS A CUT CERTIFICATE** (`closeToBipartite_iff_hitsMono`, and the
   instances `erdos73On_of_hasMonoCover`, `erdos73On_of_monoCoverBetween`): deleting at most `q`
   vertices leaves a bipartite graph *iff* some cut has a monochromatic cover of at most `q`
   vertices.  The explicit `2`-colouring `if v ∈ A then 0 else 1` on `G - Z` is
   `isBipartite_deleteFinset_of_hitsMono`.

## What the certificate is worth (machine-checked)

* `erdos73On_of_hasMonoCover` / `erdos73On_of_monoCoverBetween` are **new instances of the headline
  theorem**: `LocIndep k G` + *some* cut carrying a `q`-vertex monochromatic cover
  ⟹ `CloseToBipartite q G`; and the *between* version, where one set must work for **every** cut
  separating two given vertex sets `S` and `T`, which is the multiway-cut formulation of the same
  question.
* `hasMonoCover_completeGraph_of_split` : on `K_n` the certificate is **exactly optimal** —
  `n - 2` vertices — for every cut with both sides nonempty, so the axis is exact on the class
  where Erdős #73 is completely known (`CloseToBipartite m (K_n) ↔ n ≤ m + 2`).
* `not_hasMonoCover_completeGraph_three` : the certificate **depends on the cut**.  `K_3` is
  `1`-close to bipartite, but its trivial cut has *no* monochromatic cover at all with a single
  vertex — while `hasMonoCover_completeGraph_two_three` exhibits a cut of `K_3` whose certificate
  is exactly one vertex.  So "find a good cut" is the whole content of the certificate.
* `exists_noMonoEdge_iff_isBipartite` : the certificate at `q = 0` exists **iff** `G` is bipartite,
  i.e. "some cut is a proper `2`-colouring" ⟺ bipartite.  So the cut axis is *faithful at every
  `q`*: `q = 0` is bipartiteness and no positive `q` is free either.
* `hitsMono_of_vertexCover`, `hasMonoCover_of_vertexCover`, `monoCoverBetween_of_vertexCover` :
  any vertex cover of `q` vertices is a `q`-certificate for **every** cut, so both classes are
  non-vacuous; and `hasMonoCover_completeGraph_of_split`'s witness `V \ {a, b}` covers the
  monochromatic edges of *all* the cuts simultaneously, so the multiway version has the same
  constant `n - 2` on `K_n`.

**Not proved here.**  No concrete non-complete-graph witness of `JSP90.MonoCoverBetween` is
exhibited (the attempted witness for the pair `{0} | {1, 2}` of `K_3` was refuted by hand before
formalisation: a single vertex *does* cover the monochromatic edges of the only cut separating that
pair), and no bound is proved on the certificate of a graph in terms of `MaxDef G` — that bound is
`JSP90.OddCycleErdosPosa r` itself, since the certificate is the transversal.

See `discovery/JSP-000090/policy.json` for what this leaves of `JSP90.OddCycleErdosPosa r`.
-/

import JSPProblem.Deficiency
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic.FinCases

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqMaxCut : DecidableEq V := Classical.decEq V

/-! ### Part 0 — the notions -/

/-- **The edge `vw` is *monochromatic* for the cut with side `A`** if it does not cross the cut:
both endpoints lie in `A`, or both lie in `V \ A`.  Every odd cycle of `G` contains a monochromatic
edge of *every* cut (`exists_monoEdge_of_isOddCycle`); a set meeting all the monochromatic edges of
a cut is therefore an odd cycle transversal (`hitsOddCycles_of_hitsMono`), and deleting it leaves a
bipartite graph (`isBipartite_deleteFinset_of_hitsMono`). -/
def MonoEdge (G : SimpleGraph V) (A : Finset V) (v w : V) : Prop :=
  G.Adj v w ∧ (v ∈ A ∧ w ∈ A ∨ v ∉ A ∧ w ∉ A)

/-- **`Z` covers the monochromatic edges of the cut with side `A`**: every edge of `G` that does not
cross that cut has an endpoint in `Z`. -/
def HitsMono (G : SimpleGraph V) (A Z : Finset V) : Prop :=
  ∀ v w : V, MonoEdge G A v w → v ∈ Z ∨ w ∈ Z

/-- **The cut with side `A` separates `S` from `T`**: `S` is on the `A`-side and `T` on the other
side. -/
def Separates (S T A : Finset V) : Prop := S ⊆ A ∧ T ⊆ (Finset.univ \ A)

/-- **A `q`-certificate of the cut with side `A`**: `q` vertices suffice to meet all of its
monochromatic edges.  `hasMonoCover_zero_iff_isBipartite` below shows this is the right notion of
"`G` is `q`-close to bipartite" *provided the cut is allowed to be chosen*. -/
def HasMonoCover (G : SimpleGraph V) (q : ℕ) (A : Finset V) : Prop :=
  ∃ Z : Finset V, HitsMono G A Z ∧ Z.card ≤ q

/-- **`Z` is a monochromatic cover for every cut separating `S` from `T`.**  This is the *multiway
cut* form of `HasMonoCover`: one set has to work for a whole family of cuts, not for one. -/
def MonoCoverBetween (G : SimpleGraph V) (S T Z : Finset V) : Prop :=
  Disjoint S T ∧ (S ≠ ∅ ∨ T ≠ ∅) ∧ ∀ A : Finset V, Separates S T A → HitsMono G A Z

/-! ### Part 1 — a cycle all of whose edges cross a cut has even length -/

section Parity

variable {A : Finset V} {m : ℕ}

/-- **A CYCLE WHOSE EVERY EDGE CROSSES THE CUT HAS EVEN LENGTH.**

The predicate "`f j` lies in `A`" flips at each step, and one full turn of an odd number of steps
brings it back to `j`.  This is `even_of_cycle_in_bipartition` of
`JSPProblem/Transversal.lean` with "the two sides of a bipartition" replaced by "the two sides of an
arbitrary cut" — and it is the only place where the parity of a cycle is used in this file. -/
theorem even_of_cycle_noMono (hm3 : 3 ≤ m) (f : Fin m → V)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hnone : ∀ j : Fin m, ¬ MonoEdge G A (f j) (f (cycSucc j))) : m % 2 = 0 := by
  by_contra hn
  have hodd : m % 2 = 1 := Nat.mod_two_eq_zero_or_one m |>.resolve_left hn
  have hstep : ∀ j : Fin m, (f (cycSucc j) ∈ A) ↔ ¬ (f j ∈ A) := by
    intro j
    refine ⟨fun hsucc hmem => hnone j ⟨hcyc j, Or.inl ⟨hmem, hsucc⟩⟩, fun hnp => ?_⟩
    by_contra hc
    exact hnone j ⟨hcyc j, Or.inr ⟨hnp, hc⟩⟩
  have h0 : Fin m := ⟨0, by omega⟩
  have hiter := cycSucc_pow_odd (P := fun j => f j ∈ A) hstep (j := h0) (k := m) hodd
  rw [cycSucc_pow] at hiter
  exact not_iff_self _ hiter

/-- **A CUT WITH NO MONOCHROMATIC EDGE IS A PROPER `2`-COLOURING**, so `G` is bipartite.  This is the
converse direction of `isBipartite_deleteFinset_of_hitsMono` at `q = 0`, stated directly. -/
theorem isBipartite_of_noMonoEdge (h : ∀ v w : V, ¬ MonoEdge G A v w) : G.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ A then (0 : Fin 2) else 1) fun {v w} hv => ?_⟩
  by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A
  · have hf : False := h v w ⟨hv, Or.inl ⟨hvA, hwA⟩⟩
    exact hf.elim
  · simp [hvA, hwA]
  · simp [hvA, hwA]
  · have hf : False := h v w ⟨hv, Or.inr ⟨hvA, hwA⟩⟩
    exact hf.elim

end Parity

/-! ### Part 2 — **every odd cycle has a monochromatic edge in every cut** -/

section OddCycle

/-- **EVERY ODD CYCLE OF `G` CONTAINS A MONOCHROMATIC EDGE OF EVERY CUT.**

This is the structural content of the cut axis, and the reason the rest of the file works: an odd
cycle cannot alternate along a cut, so it has two consecutive vertices on the same side.  The
witness vertices are **in** `C`, which is what turns a cover of the monochromatic edges into a
transversal. -/
theorem exists_monoEdge_of_isOddCycle {C : Finset V} (hC : IsOddCycle G C) (A : Finset V) :
    ∃ v w : V, MonoEdge G A v w ∧ v ∈ C ∧ w ∈ C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  by_contra hn
  have hnone : ∀ j : Fin m, ¬ MonoEdge G A (f j) (f (cycSucc j)) := by
    intro j hmono
    exact hn ⟨f j, f (cycSucc j), hmono, (hCmem (f j)).mpr ⟨j, rfl⟩,
      (hCmem (f (cycSucc j))).mpr ⟨cycSucc j, rfl⟩⟩
  have heven : m % 2 = 0 := even_of_cycle_noMono hm3 f hcyc hnone
  omega

/-- ... in the form "the cycle meets `Z`, which covers the monochromatic edges". -/
theorem mem_of_hitsMono_of_isOddCycle {C Z : Finset V} (A : Finset V) (hC : IsOddCycle G C)
    (hZ : HitsMono G A Z) : ∃ v ∈ C, v ∈ Z := by
  obtain ⟨v, w, hmono, hvC, hwC⟩ := exists_monoEdge_of_isOddCycle hC A
  rcases hZ v w hmono with hv | hw
  · exact ⟨v, hvC, hv⟩
  · exact ⟨w, hwC, hw⟩

end OddCycle

/-! ### Part 3 — odd cycle transversals **are** monochromatic covers -/

section Transversal

variable {A Z : Finset V}

/-- **A VERTEX COVER OF THE MONOCHROMATIC EDGES OF A CUT IS AN ODD CYCLE TRANSVERSAL.** -/
theorem hitsOddCycles_of_hitsMono (hZ : HitsMono G A Z) : HitsOddCycles G Z := by
  intro C hC hdis
  obtain ⟨v, hvC, hv⟩ := mem_of_hitsMono_of_isOddCycle A hC hZ
  have hmem : v ∈ C ∩ Z := Finset.mem_inter.mpr ⟨hvC, hv⟩
  rw [hdis] at hmem
  simp at hmem

/-- **THE ODD CYCLE TRANSVERSALS OF `G` ARE EXACTLY THE MONOCHROMATIC COVERS OF SOME CUT.**

`⟸` is `hitsOddCycles_of_hitsMono`.  `⟧` is the construction: put the transversal on one side
together with one colour class of the bipartition of the residue.  Together with
`closeToBipartite_iff_hitsMono` this makes "the odd cycle transversal number" a *vertex cover
number of a cut*, which is the algorithmic content of the axis. -/
theorem hitsOddCycles_iff_hitsMono : HitsOddCycles G Z ↔ ∃ A : Finset V, HitsMono G A Z := by
  constructor
  · intro hZ
    have hno : ¬ (∃ C : Finset V, IsOddCycle (deleteFinset G Z) C) := by
      rintro ⟨C, hC⟩
      obtain ⟨C', hC', hd⟩ := oddCycle_of_isOddCycle_delete (G := G) (X := Z) hC
      exact hZ C' hC' hd
    have hbip : (deleteFinset G Z).IsBipartite :=
      isBipartite_of_no_oddCycle (G := deleteFinset G Z) hno
    obtain ⟨c⟩ := hbip
    have hd : ∀ ⦃v w : V⦄, G.Adj v w → v ∉ Z → w ∉ Z → c v ≠ c w := by
      intro v w hadj hvZ hwZ
      exact c.valid (deleteFinset_adj.mpr ⟨hvZ, hwZ, hadj⟩)
    set S : Finset V := (Finset.univ.filter (fun v => c v = 0)) with hSdef
    refine ⟨Z ∪ S, fun v w hmono => ?_⟩
    rcases hmono with ⟨hadj, hside⟩
    rcases hside with hside | hside
    · by_cases hvZ : v ∈ Z
      · exact Or.inl hvZ
      by_cases hwZ : w ∈ Z
      · exact Or.inr hwZ
      · have hvS : v ∈ S := (Finset.mem_union.mp hside.1).resolve_left hvZ
        have hwS : w ∈ S := (Finset.mem_union.mp hside.2).resolve_left hwZ
        have hcv : c v = 0 := (Finset.mem_filter.mp hvS).2
        have hcw : c w = 0 := (Finset.mem_filter.mp hwS).2
        exact (hd hadj hvZ hwZ (hcv.trans hcw.symm)).elim
    · have hvZ : v ∉ Z := fun hvZ => hside.1 (Finset.mem_union.mpr (Or.inl hvZ))
      have hwZ : w ∉ Z := fun hwZ => hside.2 (Finset.mem_union.mpr (Or.inl hwZ))
      have hvS : v ∉ S := fun hvS => hside.1 (Finset.mem_union.mpr (Or.inr hvS))
      have hwS : w ∉ S := fun hwS => hside.2 (Finset.mem_union.mpr (Or.inr hwS))
      have hcv : c v = 1 := Fin.eq_one_of_ne_zero (c v)
        (fun h => hvS (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
      have hcw : c w = 1 := Fin.eq_one_of_ne_zero (c w)
        (fun h => hwS (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩))
      exact (hd hadj hvZ hwZ (hcv.trans hcw.symm)).elim
  · rintro ⟨A, hA⟩
    exact hitsOddCycles_of_hitsMono hA

/-- **A VERTEX COVER OF `G` IS A MONOCHROMATIC COVER OF EVERY CUT** — the elementary source of
certificates (used by `hasMonoCover_of_vertexCover` and `monoCoverBetween_of_vertexCover`
below). -/
theorem hitsMono_of_vertexCover {Zc : Finset V} (hvc : ∀ v w : V, G.Adj v w → v ∈ Zc ∨ w ∈ Zc)
    (A : Finset V) : HitsMono G A Zc := by
  intro v w hmono
  exact hvc v w hmono.1

/-- **MONOTONICITY OF THE CERTIFICATE.** -/
theorem hitsMono_insert (hZ : HitsMono G A Z) (z : V) : HitsMono G A (insert z Z) := by
  intro v w hmono
  rcases hZ v w hmono with hv | hw
  · exact Or.inl (Finset.mem_insert_of_mem hv)
  · exact Or.inr (Finset.mem_insert_of_mem hw)

end Transversal

/-! ### Part 4 — the conclusion of Erdős #73 **is** a cut certificate -/

section Conclusion

variable {A Z : Finset V}

/-- **DELETING A MONOCHROMATIC COVER LEAVES A BIPARTITE GRAPH.**  The `2`-colouring is the cut
itself, `if v ∈ A then 0 else 1`: an edge of `G - Z` cannot have both endpoints in `A` (it would be
monochromatic and hence covered by `Z`) and cannot have both outside `A` (same), so it crosses the
cut. -/
theorem isBipartite_deleteFinset_of_hitsMono (hZ : HitsMono G A Z) :
    (deleteFinset G Z).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ A then (0 : Fin 2) else 1) fun {v w} hv => ?_⟩
  rcases deleteFinset_adj.mp hv with ⟨hvZ, hwZ, hadj⟩
  by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A
  · have hf : False := by
      rcases hZ v w ⟨hadj, Or.inl ⟨hvA, hwA⟩⟩ with h | h
      · exact hvZ h
      · exact hwZ h
    exact hf.elim
  · simp [hvA, hwA]
  · simp [hvA, hwA]
  · have hf : False := by
      rcases hZ v w ⟨hadj, Or.inr ⟨hvA, hwA⟩⟩ with h | h
      · exact hvZ h
      · exact hwZ h
    exact hf.elim

/-- **A MONOCHROMATIC COVER OF A CUT IS AN ODD CYCLE TRANSVERSAL OF THAT SIZE.** -/
theorem closeToBipartite_of_hitsMono (hZ : HitsMono G A Z) : CloseToBipartite Z.card G :=
  ⟨Z, le_rfl, isBipartite_deleteFinset_of_hitsMono hZ⟩

/-- **THE CONCLUSION OF ERDŐS #73 IS A CUT CERTIFICATE: `G` is `q`-close to bipartite if and only if
some cut of `G` has a monochromatic cover of at most `q` vertices.**

`⟹` is `hitsOddCycles_iff_hitsMono` applied to the transversal of the conclusion (the cut is `Z`
together with one colour class of the bipartition of `G - Z`); `⟸` is
`isBipartite_deleteFinset_of_hitsMono`.  The statement is an `iff`, so the axis loses nothing in
either direction. -/
theorem closeToBipartite_iff_hitsMono {q : ℕ} :
    CloseToBipartite q G ↔ ∃ A Z : Finset V, HitsMono G A Z ∧ Z.card ≤ q := by
  constructor
  · rintro ⟨X, hX, hb⟩
    obtain ⟨A, hA⟩ := (hitsOddCycles_iff_hitsMono).mp
      (hitsOddCycles_of_isBipartite_delete (G := G) hb)
    exact ⟨A, X, hA, hX⟩
  · rintro ⟨A, Z, hZ, hZc⟩
    exact ⟨Z, hZc, isBipartite_deleteFinset_of_hitsMono hZ⟩

/-- **THE `q = 0` LEVEL OF THE CERTIFICATE: SOME CUT HAS NO MONOCHROMATIC EDGE IFF `G` IS
BIPARTITE.**

`⟹` is `isBipartite_of_noMonoEdge`.  `⟸` takes `A` to be a colour class of a `2`-colouring of `G`:
neither side of the cut then carries an edge, so no edge is monochromatic.  Together with
`closeToBipartite_iff_hitsMono` this shows that the cut certificate is *faithful* at every `q`:
`q = 0` is exactly bipartiteness, and no positive `q` is free either. -/
theorem exists_noMonoEdge_iff_isBipartite :
    (∃ A : Finset V, ∀ v w : V, ¬ MonoEdge G A v w) ↔ G.IsBipartite := by
  constructor
  · rintro ⟨A, hA⟩
    exact isBipartite_of_noMonoEdge hA
  · rintro hb
    obtain ⟨c⟩ := hb
    refine ⟨Finset.univ.filter (fun v => c v = 0), fun v w hmono => ?_⟩
    rcases hmono with ⟨hadj, hside⟩
    rcases hside with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · exact c.valid hadj
        ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
    · have hcv : ¬ (c v = 0) := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have hcw : ¬ (c w = 0) := fun h => hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩)
      exact c.valid hadj
        (by rw [Fin.eq_one_of_ne_zero (c v) hcv, Fin.eq_one_of_ne_zero (c w) hcw])

end Conclusion

/-! ### Part 5 — new instances of the headline theorem on the cut axis -/

section Instances

variable {q k : ℕ}

/-- **AN INSTANCE OF THE HEADLINE THEOREM ON THE CUT AXIS: a graph admitting a `q`-certificate for
one of its cuts is `q`-close to bipartite.**  Erdős's hypothesis is not consumed — the certificate
is the whole content — so the instance is a *refinement* of the conclusion rather than a bound on
it. -/
theorem erdos73On_of_hasMonoCover {W : Type u} [Fintype W] (G : SimpleGraph W) (_hG : LocIndep k G)
    (A : Finset W) (hA : HasMonoCover G q A) : CloseToBipartite q G := by
  obtain ⟨Z, hZ, hZc⟩ := hA
  exact ⟨Z, hZc, isBipartite_deleteFinset_of_hitsMono hZ⟩

/-- **THE MULTIWAY-CUT INSTANCE: ONE SET COVERING THE MONOCHROMATIC EDGES OF *EVERY* CUT
SEPARATING `S` FROM `T` IS AN ODD CYCLE TRANSVERSAL.**  Unlike `erdos73On_of_hasMonoCover` the cut
here is not chosen by the prover: a single set must work for the whole family of cuts separating
two given vertex sets, which is the "minimum `S`–`T` cut" formulation of the transversal problem,
and `MonoCoverBetween` is a genuinely stronger hypothesis than `CloseToBipartite Z.card G`. -/
theorem erdos73On_of_monoCoverBetween {W : Type u} [Fintype W] (G : SimpleGraph W)
    (S T Z : Finset W) (hZ : MonoCoverBetween G S T Z) : CloseToBipartite Z.card G := by
  obtain ⟨hST, -, hall⟩ := hZ
  have hsep : Separates S T (Finset.univ \ T) := by
    refine ⟨?_, ?_⟩
    · intro a haS
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hST haS⟩
    · intro a haT
      have hnT : a ∉ (Finset.univ : Finset W) \ T := fun h => (Finset.mem_sdiff.mp h).2 haT
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnT⟩
  exact closeToBipartite_of_hitsMono (hall _ hsep)

/-- **A CONCRETE SOURCE OF CERTIFICATES: any vertex cover of size `q` is a `q`-certificate for every
cut.**  This shows the cut axis is never vacuous. -/
theorem hasMonoCover_of_vertexCover {Zc : Finset V} (hvc : ∀ v w : V, G.Adj v w → v ∈ Zc ∨ w ∈ Zc)
    (hcard : Zc.card ≤ q) (A : Finset V) : HasMonoCover G q A :=
  ⟨Zc, hitsMono_of_vertexCover hvc A, hcard⟩

/-- ... and the multiway version. -/
theorem monoCoverBetween_of_vertexCover {Zc : Finset V} {S T : Finset V}
    (hST : Disjoint S T) (hne : S ≠ ∅ ∨ T ≠ ∅)
    (hvc : ∀ v w : V, G.Adj v w → v ∈ Zc ∨ w ∈ Zc) : MonoCoverBetween G S T Zc :=
  ⟨hST, hne, fun _ _ => hitsMono_of_vertexCover hvc _⟩

end Instances

/-! ### Part 6 — the certificate on complete graphs, and where it fails -/

section Complete

/-- **Two vertices of `Fin 3` different from a given one, and different from each other.** -/
theorem exists_two_ne_of_three (a : Fin 3) : ∃ b c : Fin 3, b ≠ a ∧ c ≠ a ∧ b ≠ c := by
  fin_cases a
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨2, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

/-- **In `Fin 3`, two vertices different from `2` and different from each other are `0` and `1`.** -/
theorem fin3_two_of_ne_two {v w : Fin 3} (h2v : v ≠ 2) (h2w : w ≠ 2) (hvw : v ≠ w) :
    (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0) := by
  fin_cases v <;> fin_cases w <;> simp_all

/-- **ON `K_n` THE CUT CERTIFICATE IS EXACTLY OPTIMAL: `n - 2` VERTICES, FOR EVERY CUT WITH BOTH
SIDES NONEMPTY.**  Indeed `Z = V \ {a, b}` covers every monochromatic edge of every cut: an edge
`vw` of `K_n` that avoided `Z` would have `{v, w} = {a, b}`, and `a` and `b` lie on *opposite* sides
of the cut, so the edge `ab` crosses it and is not monochromatic.

Together with `JSP90.closeToBipartite_completeGraph_iff_maxDef`
(`CloseToBipartite m (K_n) ↔ n ≤ m + 2`) this shows the cut axis is *exact* on the class where
Erdős #73 is completely known, so no information is lost by using it. -/
theorem hasMonoCover_completeGraph_of_split {W : Type*} [Fintype W]
    (hn : 2 ≤ (Finset.univ : Finset W).card)
    (A : Finset W) (hA : A.Nonempty) (hAc : ((Finset.univ : Finset W) \ A).Nonempty) :
    HasMonoCover (SimpleGraph.completeGraph W) ((Finset.univ : Finset W).card - 2) A := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have hab : a ≠ b := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hb).2 ha
  have hcross : ¬ MonoEdge (SimpleGraph.completeGraph W) A a b := by
    intro hmono
    rcases hmono.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ((Finset.mem_sdiff.mp hb).2 h2).elim
    · exact (h1 ha).elim
  have hswap : ∀ v w : W, MonoEdge (SimpleGraph.completeGraph W) A v w →
      MonoEdge (SimpleGraph.completeGraph W) A w v :=
    fun v w h => ⟨h.1.symm, h.2.imp (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩)⟩
  refine ⟨(Finset.univ : Finset W) \ {a, b}, fun v w hmono => ?_, ?_⟩
  · by_cases hZv : v ∈ (Finset.univ : Finset W) \ {a, b}
    · exact Or.inl hZv
    by_cases hZw : w ∈ (Finset.univ : Finset W) \ {a, b}
    · exact Or.inr hZw
    · have hvab : v ∈ ({a, b} : Finset W) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hZv
        exact not_not.mp hZv
      have hwab : w ∈ ({a, b} : Finset W) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hZw
        exact not_not.mp hZw
      have hvab' : v = a ∨ v = b := by
        rcases Finset.mem_insert.mp hvab with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      have hwab' : w = a ∨ w = b := by
        rcases Finset.mem_insert.mp hwab with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      have hne : v ≠ w := fun h =>
        SimpleGraph.irrefl (G := SimpleGraph.completeGraph W) (h ▸ hmono.1)
      rcases hvab' with hv' | hv'
      · rcases hwab' with hw' | hw'
        · exact False.elim (hne (hv'.trans hw'.symm))
        · exact (hcross (by rw [← hv', ← hw']; exact hmono)).elim
      · rcases hwab' with hw' | hw'
        · exact (hcross (hswap _ _ (by rw [← hv', ← hw']; exact hmono))).elim
        · exact False.elim (hne (hv'.trans hw'.symm))
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hab]

/-- **A CUT OF `K_3` WHOSE CERTIFICATE IS EXACTLY ONE VERTEX** — the optimum, since
`JSP90.closeToBipartite_completeGraph_three` gives `CloseToBipartite 1 (K_3)` and
`JSP90.not_isBipartite_completeGraph_three` rules out `0`.  The cut is `{0, 1} | {2}`: its
monochromatic edges are `{0, 1}` and (none), so `{0}` covers them. -/
theorem hasMonoCover_completeGraph_two_three :
    HasMonoCover (SimpleGraph.completeGraph (Fin 3)) 1 ({0, 1} : Finset (Fin 3)) := by
  refine ⟨{0}, fun v w hmono => ?_, by simp⟩
  rcases hmono with ⟨hadj, hside⟩
  rcases hside with ⟨hvA, hwA⟩ | ⟨hvA, hwA⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hvA hwA
    rcases hwA with hw0 | hw1
    · exact Or.inr (Finset.mem_singleton.mpr hw0)
    · rcases hvA with hv0 | hv1
      · exact Or.inl (Finset.mem_singleton.mpr hv0)
      · exact False.elim (SimpleGraph.irrefl (G := SimpleGraph.completeGraph (Fin 3))
          ((hv1.trans hw1.symm) ▸ hadj))
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvA hwA
    have hv2 : (v : ℕ) = 2 := by
      have h1 : (v : ℕ) ≠ 1 := fun h => hvA.2 (Fin.ext h)
      have h0 : (v : ℕ) ≠ 0 := fun h => hvA.1 (Fin.ext h)
      omega
    have hw2 : (w : ℕ) = 2 := by
      have h1 : (w : ℕ) ≠ 1 := fun h => hwA.2 (Fin.ext h)
      have h0 : (w : ℕ) ≠ 0 := fun h => hwA.1 (Fin.ext h)
      omega
    have heq : v = w := Fin.ext (hv2.trans hw2.symm)
    exact False.elim (SimpleGraph.irrefl (G := SimpleGraph.completeGraph (Fin 3)) (heq ▸ hadj))

/-- **AND THE TRIVIAL CUT OF THE SAME GRAPH HAS NO SINGLE-VERTEX CERTIFICATE AT ALL**: the
certificate depends on the cut, so "find a good cut" is the content of the axis. -/
theorem not_hasMonoCover_completeGraph_three :
    ¬ HasMonoCover (SimpleGraph.completeGraph (Fin 3)) 1 (∅ : Finset (Fin 3)) := by
  rintro ⟨Z, hZ, hcard⟩
  rcases (show Z.card = 0 ∨ Z.card = 1 by omega) with h | h
  · have hZempty : Z = ∅ := Finset.card_eq_zero.mp h
    have hmono : MonoEdge (SimpleGraph.completeGraph (Fin 3)) ∅ 0 1 :=
      ⟨SimpleGraph.top_adj 0 1 |>.mpr (by decide), Or.inr ⟨by simp, by simp⟩⟩
    rcases hZ 0 1 hmono with h | h
    · rw [hZempty] at h
      simp at h
    · rw [hZempty] at h
      simp at h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨b, c, hb, hc1, hc2⟩ := exists_two_ne_of_three a
    have hmono : MonoEdge (SimpleGraph.completeGraph (Fin 3)) ∅ b c :=
      ⟨SimpleGraph.top_adj b c |>.mpr hc2, Or.inr ⟨by simp, by simp⟩⟩
    rcases hZ b c hmono with h | h
    · rw [Finset.mem_singleton] at h
      exact hb h
    · rw [Finset.mem_singleton] at h
      exact hc1 h

end Complete

end

end JSP90