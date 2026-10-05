import JSPProblem.TriCount

/-!
# JSP-000090, round 167 -- `JSPProblem/TriFiveLang.lean`: the `Fin 8` language of the eight-vertex
## triangle case, over a **five**-point residue `K_{2,3}`

Attack family 88 (the EIGHT-VERTEX INSTANCE).  This file is the language; the counting step
`JSP90.loc8_lemma` is in `lean/JSPProblem/TriFive.lean`, whose sixty-four `decide` pieces live in
`TriFiveA`, `TriFiveB`, `TriFiveC`, `TriFiveD` (sixteen each, chained, because one process holding
all sixty-four proofs is killed by the OOM killer -- exit code 137 -- as it was in round 164).

Round 166 closed the seven-vertex axis; its triangle case rests on `JSP90.loc7_lemma`, the counting
step for a residue of **four** points (four cells of `G[X]`, three neighbour sets carried as
functions `Fin 3 -> Fin 4 -> Bool`).  At `|V| = 8` the residue of a triangle has **five** points, and
`JSP90.card_cls_ge_two` forces the two colour classes to have sizes `2` and `3`, so `G[X]` sits inside
`K_{2,3}` with **six** cells.  Here:

* the residue is carried by the points `0 … 4`, the colour classes being `{0,1}` and `{2,3,4}`;
* the triangle `T` is carried by `5, 6, 7`;
* the six cells of `G[X]` are the number `A : Fin 64` (cell `3 * p + (q - 2)` is the pair `p, q`);
* each neighbour set is carried by a **mask** `s : Fin 32` (bit `x` says "`x` lies in `S`"), so every
  test below is `Nat` arithmetic rather than `Fin` pattern matching -- that is what keeps the
  sixty-four `decide` pieces inside the budget.

Two `Bool`s carry the content: `JSP90.badM A s = true` is "`no proper two-colouring of the residue
makes the neighbour set `s` monochromatic`", i.e. the vertex is **bad**, and
`JSP90.badSix A s0 s1 s2 = true` is "`some six-element subset of the eight has no independent
triple`".  Part 1 states the readings the transfer needs.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The language -/

/-- the mask of the neighbour set of the `t`-th vertex of the triangle -/
def sOf (s0 s1 s2 t : Nat) : Nat := if t = 0 then s0 else if t = 1 then s1 else s2

/-- bit `x` of the mask `s`: "`x` lies in the neighbour set" -/
def sBit (s x : Nat) : Bool := decide (s.testBit x = true)

/-- the cell `(p, q)` between the colour classes `{0,1}` and `{2,3,4}`, for `p, q < 5`; `false`
inside a colour class -/
def crossM (A : Fin 64) (p q : Nat) : Bool :=
  if p < 2 then (if q < 2 then false else A.val.testBit (3 * p + (q - 2)))
  else if q < 2 then A.val.testBit (3 * q + (p - 2)) else false

/-- the adjacency of the eight vertices: `0 … 4` are the residue, `5, 6, 7` the triangle -/
def adj8n (A : Fin 64) (s0 s1 s2 i j : Nat) : Bool :=
  if i < 5 then
    (if j < 5 then crossM A i j else if 5 ≤ j then sBit (sOf s0 s1 s2 (j - 5)) i else false)
  else
    (if j < 5 then sBit (sOf s0 s1 s2 (i - 5)) j else if 5 ≤ j then decide (i ≠ j) else false)

/-- an independent triple at three distinct points -/
def ind3n (A : Fin 64) (s0 s1 s2 a b c : Nat) : Bool :=
  decide (a < b) && decide (b < c)
    && ! adj8n A s0 s1 s2 a b && ! adj8n A s0 s1 s2 a c && ! adj8n A s0 s1 s2 b c

/-- **`X` CONTAINS AN INDEPENDENT TRIPLE**, `X` a mask over the eight vertices -/
def hasInd3m (A : Fin 64) (s0 s1 s2 X : Nat) : Bool :=
  (List.range 8).any fun a => ((X >>> a) &&& 1 == 1) && (List.range 8).any fun b =>
    (((X >>> b) &&& 1 == 1) && ! adj8n A s0 s1 s2 a b && (List.range 8).any fun c =>
      ((X >>> c) &&& 1 == 1) && ind3n A s0 s1 s2 a b c)

/-- **THE THREE SIX-ELEMENT SUBSETS THAT COVER EVERY CONFIGURATION**
(`discovery/JSP-000090/r167f.c`): the triangle `5, 6, 7` together with the two points `0, 1` of the
smaller colour class and one point `2`, `3` or `4` of the larger.  Each of them is a witness (a
six-element subset with no independent triple) for `40 128` of the `61 236` configurations satisfying
the three hypotheses, and together they cover all of them. -/
def sixMasks : List Nat := [231, 235, 243]

/-- **SOME SIX-ELEMENT SUBSET OF THE EIGHT HAS NO INDEPENDENT TRIPLE** -/
def badSix (A : Fin 64) (s0 s1 s2 : Nat) : Bool :=
  sixMasks.any fun X => ! hasInd3m A s0 s1 s2 X

/-- the neighbours of the point `p` inside `{2,3,4}`, as a mask with the weights of a colouring -/
def nbrMask (A : Fin 64) (p : Nat) : Nat :=
  (if A.val.testBit (3 * p) then 4 else 0) + (if A.val.testBit (3 * p + 1) then 8 else 0)
    + (if A.val.testBit (3 * p + 2) then 16 else 0)

/-- the mask `s` is monochromatic under the colouring `i` -/
def okMono (i s : Nat) : Bool := (i &&& s) == 0 || (i &&& s) == s

/-- the colouring `i` separates the point `p` from all of its neighbours, `n` being the neighbour
mask of `p`: the neighbours carry the other colour -/
def okCol (i p n : Nat) : Bool := (i &&& n) == (if i.testBit p then 0 else n)

/-- the colouring `i` of the five residue points is **proper** for the cells `A` -/
def properM (A : Fin 64) (i : Nat) : Bool := okCol i 0 (nbrMask A 0) && okCol i 1 (nbrMask A 1)

/-- the mask `s` is **not** monochromatic under any proper colouring, i.e. the vertex whose
neighbour set is `s` is **bad**.  Only half of the colourings are tested, because `i` and `31 - i`
are proper together and agree on monochromaticity. -/
def badM (A : Fin 64) (s : Nat) : Bool :=
  ! ((List.range 16).any fun i => okMono i s && properM A i)

/-- the mask `s` meets both colour classes -/
def meetBoth (s : Nat) : Bool :=
  (s.testBit 0 || s.testBit 1) && (s.testBit 2 || s.testBit 3 || s.testBit 4)

/-- the three masks have empty triple intersection -/
def tripleEmpty (s0 s1 s2 : Nat) : Bool :=
  (List.range 5).all fun i => decide ((s0.testBit i && s1.testBit i && s2.testBit i) = false)

/-- **THE THREE HYPOTHESES**, in the order the kernel is to pay for them: the two cheap ones
first, badness last. -/
def hyps8n (A : Fin 64) (s0 s1 s2 : Nat) : Bool :=
  (meetBoth s0 && meetBoth s1 && meetBoth s2) && tripleEmpty s0 s1 s2
    && badM A s0 && badM A s1 && badM A s2

/-- **NO INDEPENDENT TRIPLE IN `X_i = {0, 1} + {i} + {5, 6, 7}`**, for `i` one of `2, 3, 4` -- the cheap
form of `! hasInd3m A s0 s1 s2 (231 + ...)`.

`X_i` has six points and the triangle `5, 6, 7` is a clique, so an independent triple inside `X_i`
contains at most one point of the triangle and therefore at least two of `0, 1, i`: ten candidates,
and this is the ten guarded pairs.  It is this function, and not the `512`-iteration search of
`JSP90.hasInd3m`, that `JSP90.loc8cond` evaluates, which is what keeps the sixty-four `decide` pieces
inside the memory budget of this machine. -/
def noInd36 (A : Fin 64) (s0 s1 s2 : Nat) (i : Nat) : Bool :=
  ! ind3n A s0 s1 s2 0 1 i && ! ind3n A s0 s1 s2 0 1 5 && ! ind3n A s0 s1 s2 0 1 6
    && ! ind3n A s0 s1 s2 0 1 7 && ! ind3n A s0 s1 s2 0 i 5 && ! ind3n A s0 s1 s2 0 i 6
    && ! ind3n A s0 s1 s2 0 i 7 && ! ind3n A s0 s1 s2 1 i 5 && ! ind3n A s0 s1 s2 1 i 6
    && ! ind3n A s0 s1 s2 1 i 7

/-- **THE THREE SIX-ELEMENT SUBSETS, IN THE CHEAP FORM.** -/
def badSix' (A : Fin 64) (s0 s1 s2 : Nat) : Bool :=
  noInd36 A s0 s1 s2 2 || noInd36 A s0 s1 s2 3 || noInd36 A s0 s1 s2 4

/-- the counting step: no configuration of the language is a counterexample -/
def loc8cond (A : Fin 64) (s0 s1 s2 : Nat) : Bool :=
  ! hyps8n A s0 s1 s2 || badSix' A s0 s1 s2

/-- **THE TRIANGLE IS A CLIQUE**, in the language: the points `5, 6, 7` are pairwise adjacent, so an
independent triple contains **at most one** of them.  This is what makes the cheap reading of the
six-element subsets possible. -/
theorem clique_T : ∀ (A : Fin 64) (s0 s1 s2 : Fin 32) (u v : Nat), 5 ≤ u → 5 ≤ v → u < v →
    adj8n A s0.val s1.val s2.val u v = true := by
  intro A s0 s1 s2 u v hu hv huv
  have hne : u ≠ v := by omega
  have hnu : ¬ (u < 5) := by omega
  have hnv : ¬ (v < 5) := by omega
  simp [adj8n, hnu, hnv, hv, hne]

/-! ## The readings, which are what the transfer of the next round consumes

`JSP90.badM A s = true` is *the* badness of the vertex whose neighbour set is the mask `s`: no proper
two-colouring of the residue makes `s` monochromatic.  The transfer hypothesis is the graph-level
"`G[X + {t}]` is not bipartite"; these lemmas are the bridge, the delicate part being that the
`Bool` tests only half of the colourings (`i` and `31 - i` are proper together and agree on
monochromaticity, `JSP90.badM_half`).  `JSP90.badSix A s0 s1 s2 = true` says that one of the three
six-element subsets of `JSP90.sixMasks` contains no independent triple, which is what Erdős
hypothesis forbids (`JSP90.badSix_of_all`).

Note the shape of the `decide` statements below: every quantifier has to live *inside* the
statement, because `decide` cannot close a goal with free local variables. -/

/-- **BADNESS, IN THE READING THE TRANSFER NEEDS.**  `badM A s = true` iff no colouring `i < 16`
which is proper for the cells `A` makes the mask `s` monochromatic -- the reading a transfer needs,
because such an `i` *is* a two-colouring of the residue read off the masks. -/
theorem badM_correct : ∀ (A : Fin 64) (s : Fin 32), badM A s.val = true ↔
    ((List.range 16).all fun i => ! (okMono i s.val && properM A i)) = true := by decide

/-- **BADNESS, READ FORWARD**: a proper colouring with `s` monochromatic makes the vertex good. -/
theorem badM_correct' : ∀ (A : Fin 64) (s : Fin 32), badM A s.val = false ↔
    ((List.range 16).any fun i => okMono i s.val && properM A i) = true := by decide

/-- **HALF THE COLOURINGS ARE ENOUGH.**  `badM` tests `i < 16` only, and that is equivalent to the
statement over all thirty-two colourings. -/
theorem badM_half : ∀ (A : Fin 64) (s : Fin 32), badM A s.val = true ↔
    ((List.range 32).all fun i => ! (okMono i s.val && properM A i)) = true := by decide

theorem badM_of_all (A : Fin 64) (s : Fin 32)
    (h : ∀ i ∈ (List.range 16), ¬ (okMono i s.val && properM A i) = true) :
    badM A s.val = true := by
  have h' : (List.range 16).any (fun i => okMono i s.val && properM A i) = false :=
    List.any_eq_false.mpr (fun i hi => by simpa using h i hi)
  unfold badM
  rw [h']
  rfl

theorem exists_of_not_badM (A : Fin 64) (s : Fin 32) (h : badM A s.val = false) :
    ∃ i ∈ (List.range 16), (okMono i s.val && properM A i) = true := by
  have h' : (List.range 16).any (fun i => okMono i s.val && properM A i) = true := by
    unfold badM at h
    cases hb : ((List.range 16).any (fun i => okMono i s.val && properM A i)) <;>
      simp_all
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.mp h'
  exact ⟨i, hi, hb⟩

theorem badSix_of_all (A : Fin 64) (s0 s1 s2 : Fin 32)
    (h : ∀ X ∈ sixMasks, hasInd3m A s0.val s1.val s2.val X = true) :
    badSix A s0.val s1.val s2.val = false := by
  unfold badSix
  refine List.any_eq_false.mpr (fun X hX => ?_)
  have hX := h X hX
  cases hb : hasInd3m A s0.val s1.val s2.val X <;> simp_all

theorem exists_of_badSix (A : Fin 64) (s0 s1 s2 : Fin 32) (h : badSix A s0.val s1.val s2.val = true) :
    ∃ X ∈ sixMasks, hasInd3m A s0.val s1.val s2.val X = false := by
  have h' : (sixMasks.any fun X => ! hasInd3m A s0.val s1.val s2.val X) = true := h
  obtain ⟨X, hX, hXb⟩ := List.any_eq_true.mp h'
  exact ⟨X, hX, by simpa using hXb⟩

theorem hasInd3m_of_indep3 (A : Fin 64) (s0 s1 s2 : Fin 32) (X a b c : Nat) (hab : a < b)
    (hbc : b < c) (hc : c < 8) (hXa : ((X >>> a) &&& 1 == 1) = true)
    (hXb : ((X >>> b) &&& 1 == 1) = true) (hXc : ((X >>> c) &&& 1 == 1) = true)
    (hab' : (! adj8n A s0.val s1.val s2.val a b) = true)
    (hac' : (! adj8n A s0.val s1.val s2.val a c) = true)
    (hbc' : (! adj8n A s0.val s1.val s2.val b c) = true) :
    hasInd3m A s0.val s1.val s2.val X = true := by
  have hmem_a : a ∈ (List.range 8) := by rw [List.mem_range]; omega
  have hmem_b : b ∈ (List.range 8) := by rw [List.mem_range]; omega
  have hmem_c : c ∈ (List.range 8) := by rw [List.mem_range]; exact hc
  have hlt1 : (decide (a < b)) = true := decide_eq_true_eq.mpr hab
  have hlt2 : (decide (b < c)) = true := decide_eq_true_eq.mpr hbc
  have h12 : (decide (a < b) && decide (b < c)) = true :=
    Bool.and_eq_true_iff.mpr ⟨hlt1, hlt2⟩
  have h3 : ((decide (a < b) && decide (b < c))
      && (! adj8n A s0.val s1.val s2.val a b)) = true :=
    Bool.and_eq_true_iff.mpr ⟨h12, hab'⟩
  have h4 : (((decide (a < b) && decide (b < c))
      && (! adj8n A s0.val s1.val s2.val a b))
      && (! adj8n A s0.val s1.val s2.val a c)) = true :=
    Bool.and_eq_true_iff.mpr ⟨h3, hac'⟩
  have hind : ind3n A s0.val s1.val s2.val a b c = true :=
    Bool.and_eq_true_iff.mpr ⟨h4, hbc'⟩
  have hinner : Bool.and ((X >>> c) &&& 1 == 1) (ind3n A s0.val s1.val s2.val a b c) = true :=
    Bool.and_eq_true_iff.mpr ⟨hXc, hind⟩
  have hmid : Bool.and (Bool.and ((X >>> b) &&& 1 == 1) (! adj8n A s0.val s1.val s2.val a b))
      ((List.range 8).any (fun c => Bool.and ((X >>> c) &&& 1 == 1)
        (ind3n A s0.val s1.val s2.val a b c))) = true := by
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · exact Bool.and_eq_true_iff.mpr ⟨hXb, hab'⟩
    · exact List.any_eq_true.mpr ⟨c, hmem_c, hinner⟩
  refine List.any_eq_true.mpr ⟨a, hmem_a, ?_⟩
  refine Bool.and_eq_true_iff.mpr ⟨hXa, ?_⟩
  refine List.any_eq_true.mpr ⟨b, hmem_b, ?_⟩
  exact hmid

theorem mem_sixMasks : ∀ i : Nat, i < 8 →
    ((231 >>> i) &&& 1 == 1 ↔ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6 ∨ i = 7) ∧
    ((235 >>> i) &&& 1 == 1 ↔ i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7) ∧
    ((243 >>> i) &&& 1 == 1 ↔ i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) := by
  decide

/-- **THE MASKS, IN THE READING THE TRANSFER NEEDS**: bit `x` of the mask `s` is "`x` lies in the
neighbour set". -/
theorem sBit_correct (s x : Nat) (hx : x < 5) : sBit s x = true ↔ s.testBit x = true := by
  simp [sBit, hx]

end JSP90
