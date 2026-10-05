import JSPProblem.ThreeOrder

/-!
# JSP-000090, round 164 — `JSPProblem/TriCount.lean`: **THE COUNTING STEP OF THE TRIANGLE CASE**

Attack family 86.  This round executes the concrete next bet of round 163 (`policy.json`): the
`|X| = 4` sub-case of MISSING LEMMA 1, the *only* open case of the sharp seven-vertex axis, which
round 162 isolated in `JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase`:

```lean
LocIndep 1 G → Fintype.card V ≤ 7 → G.IsNClique 3 T → (deleteFinset G T).IsBipartite →
  ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
```

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
   neighbour sets meeting both classes: `JSP90.loc7_lemma`.  It is stated in the `Fin 7` language
   (`X = {0,1,2,3}` with classes `{0,1}` and `{2,3}`, `T = {4,5,6}` a clique, `t` joined to `S t`) and
   **closed by `decide`**, so the Lean kernel itself verifies the whole case analysis.  Its statement:

   > three bad vertices of a triangle over a bipartite four-element residue, the three neighbour sets
   > meeting both colour classes, and the three sets with empty triple intersection ⟹ some vertex of
   > the seven is avoided by **no** independent set of three vertices.

   Erdős's hypothesis supplies such an independent triple for every six-element subset, and the
   transfer back to `V` is `JSP90.transfer_cover`, so the two contradict.

## What this file proves

* `JSP90.loc7_lemma` — the counting step above, **by `decide`** (`decide` on the `Fin 7` language;
  no `native_decide`, so the proof is verified by the Lean kernel and the axiom list is unchanged).
* `JSP90.hyps_of`, `JSP90.exists_triple_of_hasTripleAvoiding` — the glue between the `Fin 7`
  language and the hypotheses of `loc7_lemma`, and the reading of a witness back.
* `JSP90.isBipartite_of_adjIn_mono`, `JSP90.exists_adjIn_color`, `JSP90.card_cls_ge_two` — steps 1
  and 2 above, in general form.
* `JSP90.bitCol`, `JSP90.opp2` — the two-colouring apparatus.

The transfer from a graph to the `Fin 7` language (building the four cells `A`, the three neighbour
sets `S`, the correspondence `adj7`, and the exclusion of the `|V| = 7` case) is being completed;
`policy.json` records it as the next bet.
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

/-- All sixteen colourings of `X` by two colours. -/
def allCol : List (Fin 4 → Bool) :=
  List.ofFn fun m : Fin 16 => fun i : Fin 4 => decide ((m.val >>> i.val) &&& 1 == 1)

/-- A proper two-colouring of `G[X]`. -/
def properX (A : Fin 4 → Bool) (c : Fin 4 → Bool) : Bool :=
  !((c 0 && (cross A 0 ⟨2, by decide⟩ || cross A 0 ⟨3, by decide⟩))
    || (c 1 && (cross A 1 ⟨2, by decide⟩ || cross A 1 ⟨3, by decide⟩)))

/-- `S t` is monochromatic under the colouring `c` of `X`. -/
def monoS (S : Fin 3 → Fin 4 → Bool) (t : Fin 3) (c : Fin 4 → Bool) : Bool :=
  !((S t 0 && S t 1 && (c 0 != c 1)) || (S t 2 && S t 3 && (c 2 != c 3))
    || (S t 0 && S t 2 && (c 0 != c 2)) || (S t 0 && S t 3 && (c 0 != c 3))
    || (S t 1 && S t 2 && (c 1 != c 2)) || (S t 1 && S t 3 && (c 1 != c 3))
    || (S t 1 && S t 0 && (c 1 != c 0)) || (S t 3 && S t 2 && (c 3 != c 2))
    || (S t 2 && S t 0 && (c 2 != c 0)) || (S t 3 && S t 0 && (c 3 != c 0))
    || (S t 2 && S t 1 && (c 2 != c 1)) || (S t 3 && S t 1 && (c 3 != c 1)))

/-- **THE VERTEX `t` OF `T` IS BAD**: `G[X + {t}]` is not bipartite, i.e. no proper two-colouring of
`G[X]` makes `S t` monochromatic. -/
abbrev bad8 (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (t : Fin 3) : Prop :=
  ∀ c : Fin 4 → Bool, ¬ (properX A c = true ∧ monoS S t c = true)

/-- The hypotheses of the counting step: the three sets have empty triple intersection, each `S t`
meets both colour classes, and each `t` is bad. -/
def hyps (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) : Bool :=
  ((List.finRange 4).all (fun i => decide ((S 0 i && S 1 i && S 2 i) = false))
    && (List.finRange 3).all (fun t => (S t 0 || S t 1) && (S t 2 || S t 3)))
    && (List.finRange 3).all (fun t => decide (bad8 A S t))

/-- **THERE IS AN INDEPENDENT TRIPLE AVOIDING `z`.** -/
def hasTripleAvoiding (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool) (z : Fin 7) : Bool :=
  (List.finRange 7).any fun a => (List.finRange 7).any fun b =>
    (decide (a ≠ b) &&
      ((List.finRange 7).any fun c =>
        (decide (c ≠ a) &&
          (decide (c ≠ b) &&
            (indep3 A S a b c &&
              (decide (a ≠ z) && (decide (b ≠ z) && decide (c ≠ z))))))))

/-- **THE FOUR-ELEMENT COUNTING STEP, IN THE `Fin 7` LANGUAGE.**  Three bad vertices of a triangle
over a bipartite four-element residue, the three neighbour sets meeting both colour classes, and
the three sets with empty triple intersection: then some vertex of the seven is avoided by no
independent set of three vertices, which contradicts Erdős's hypothesis.

The statement is closed by `decide`, so the Lean kernel itself verifies the finite case analysis. -/
theorem loc7_lemma : ∀ (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool),
    hyps A S = true → ¬ ((∀ z : Fin 7, hasTripleAvoiding A S z = true)) := by
  decide

/-- **AN INDEPENDENT TRIPLE AVOIDING `z` GIVES THREE POINTS.** -/
theorem exists_triple_of_hasTripleAvoiding {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool}
    {z : Fin 7} (h : hasTripleAvoiding A S z = true) :
    ∃ a b c : Fin 7, indep3 A S a b c = true ∧ a ≠ z ∧ b ≠ z ∧ c ≠ z := by
  unfold hasTripleAvoiding at h
  obtain ⟨a, -, ha⟩ := List.any_eq_true.mp h
  obtain ⟨b, -, hb⟩ := List.any_eq_true.mp ha
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hab, hcrest⟩ := hb
  obtain ⟨c, -, hc⟩ := List.any_eq_true.mp hcrest
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hcb, hrest⟩ := hc
  obtain ⟨hcc, hrest2⟩ := hrest
  obtain ⟨hind, hrest3⟩ := hrest2
  obtain ⟨hz1, hrest4⟩ := hrest3
  obtain ⟨hz2, hz3⟩ := hrest4
  exact ⟨a, b, c, hind, of_decide_eq_true hz1, of_decide_eq_true hz2, of_decide_eq_true hz3⟩

/-- The hypotheses of `loc7_lemma` are exactly the three conditions of the counting step. -/
theorem hyps_of {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool}
    (h1 : ∀ i : Fin 4, S 0 i = true → S 1 i = true → S 2 i = true → False)
    (h2 : ∀ t : Fin 3, S t 0 = true ∨ S t 1 = true)
    (h3 : ∀ t : Fin 3, S t 2 = true ∨ S t 3 = true)
    (h4 : ∀ t : Fin 3, bad8 A S t) :
    hyps A S = true := by
  have h1' : (List.finRange 4).all (fun i => decide ((S 0 i && S 1 i && S 2 i) = false)) = true := by
    apply List.all_eq_true.mpr
    intro i _
    refine decide_eq_true (Bool.eq_false_of_not_eq_true ?_)
    intro hpos
    simp only [Bool.and_eq_true] at hpos
    exact h1 i hpos.1.1 hpos.1.2 hpos.2
  have h2' : (List.finRange 3).all (fun t => (S t 0 || S t 1) && (S t 2 || S t 3)) = true := by
    apply List.all_eq_true.mpr
    intro t _
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨h2 t, h3 t⟩
  have h3' : (List.finRange 3).all (fun t => decide (bad8 A S t)) = true := by
    apply List.all_eq_true.mpr
    intro t _
    exact decide_eq_true (h4 t)
  simp only [hyps, Bool.and_eq_true]
  exact ⟨⟨h1', h2'⟩, h3'⟩

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

