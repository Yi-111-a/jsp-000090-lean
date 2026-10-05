import JSPProblem.TriFiveP

/-!
# JSP-000090, round 167 -- `JSPProblem/TriFive.lean`: **THE COUNTING STEP OF THE EIGHT-VERTEX
## TRIANGLE CASE, IN THE FORM THAT IS ACTUALLY TRUE**

Attack family 88, the EIGHT-VERTEX INSTANCE (`policy.json`, round 166, `next_bet`).  Round 166 closed
the seven-vertex axis with `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`, whose triangle
case `JSP90.triCase` rests on the counting step `JSP90.loc7_lemma` of `lean/JSPProblem/TriCount.lean`
-- three bad vertices of a triangle over a **four**-point residue.  At `|V| = 8` the residue of a
triangle has **five** points, and this file records what becomes of that counting step: it is
**false** in the seven-vertex form, and this file gives the form that is true.

## The residue at `|V| = 8`

`JSP90.card_cls_ge_two` (`TriCount.lean`) forces both colour classes of the residue to have at least
two points, so the residue is `K_{2,3}`: the points `0, 1` carry one colour, the points `2, 3, 4`
the other, and the six cells of `G[X]` are the number `A : Fin 64`.  The triangle `T` is carried by
`5, 6, 7` and the three neighbour sets by **masks** `Fin 32`.  The language is
`lean/JSPProblem/TriFiveLang.lean`; the sixty-four `decide` pieces are in `TriFiveA`, `TriFiveB`,
`TriFiveC`, `TriFiveD`, sixteen each (one process holding all sixty-four proofs is killed by the OOM
killer, exit code 137, the lesson of round 164).

## The counting step of round 166 is FALSE at eight vertices

Round 166's `next_bet` predicted that "`three bad vertices of `T`, each `S t` meeting both colour
classes, empty triple intersection => some vertex of the eight is avoided by no independent triple`"
is the eight-vertex analogue of `JSP90.loc7_lemma`.  It is not: the analogue is **refuted with
23 976 counterexamples**, measured by `discovery/JSP-000090/r167b.c` and reproduced independently by
`#eval` in a scratch copy of this language:

| configurations of the language `A × s` (`2^6 · 2^15 = 2 097 152`) | count |
|---|---|
| (i) each `S t` meets both classes, (ii) `S 0 & S 1 & S 2 = {}`, (iii) every `t` **bad** | `61 236` |
| of those, with every vertex of the eight avoided by an independent triple | `23 976` |
| of those, with an independent quadruple as well | `6 444` |
| **of those, `LocIndep 1`** | **`0`** |

A counterexample of the second row: `A = 63` (the complete `K_{2,3}`) with masks `19, 10, 5` -- all
three vertices of the triangle are bad, the three neighbour sets meet both colour classes and have
empty triple intersection, and Erdős's hypothesis read on the seven-element subsets *is* satisfied.
So the seven-vertex argument cannot be repeated verbatim; the reason it cannot is the last row.

## The counting step that IS true

The last row is the content of this file.  **Erdős's full hypothesis is what kills those
configurations**, and it kills them with a *six*-element subset: for every one of the `61 236`
configurations some six-element subset of the eight has **no** independent triple (`r167c.c`:
six-element subsets are witnesses for all `61 236` of them, while subsets of size `4`, `7`, `8` are
witnesses for only `34 812`, `37 260`, `54 792`).  A greedy cover (`r167f.c`) shows that **three**
six-element subsets suffice, and they are the symmetric ones,

```
JSP90.sixMasks = [231, 235, 243] = [ T + {0,1,2},  T + {0,1,3},  T + {0,1,4} ]
```

the whole triangle together with the **two** points of the smaller colour class and **one** point of
the larger; each of the three is a witness for `40 128` of the configurations.

`JSP90.loc8_lemma` is exactly this statement, proved by `decide` sixty-four times, once for each of
the `2 ^ 6` configurations of the six cells.  It settles the triangle case at `|V| = 8` as soon as
the graph is carried into the language: `LocIndep 1` supplies an independent triple inside *each*
of the three six-element subsets, which the lemma forbids, so one of the three vertices of `T` is
good.  (In the language the conclusion is `JSP90.badSix'`, the cheap reading of the three subsets:
the triangle is a clique, `JSP90.clique_T`, so an independent triple inside `T + {0,1,i}` contains
at most one point of `T` and hence at least two of `0, 1, i` -- ten candidates, `JSP90.noInd36`.)

## What the transfer still needs

* the graph carried into the language (`xpt : Fin 5 → V`, `tpt : Fin 3 → V`, `inv : Fin 8 → V`, the
  masks, and `adj8n A s0 s1 s2 i j = decide (G.Adj (inv i) (inv j))`),
* the three hypotheses transferred, badness being the delicate one (a colouring `i < 16` of the
  residue is proper exactly when `JSP90.properM A i = true`, and then the graph-level badness says
  the mask `s t` is not monochromatic),
* the eight-vertex bridge: the residue of a triangle is bipartite at `|V| ≤ 8`.  At `|V| = 7` this
  is round 150's `JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven`; at
  `|V| = 8` it needs the five-vertex fact that a triangle-free graph on five vertices with an
  independent triple is bipartite (a `decide` over the `2 ^ 10` graphs on `Fin 5`).

Behind all of it: `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), so
`jsp_000090_main` is still deliberately **not** declared.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

/-! ## The counting step -/

/-- **READING THE COUNTING CONDITION.**  `loc8cond` is "`the three hypotheses do not hold, or the
conclusion does`", so a piece of the table plus the three hypotheses gives the conclusion. -/
theorem loc8_read (n : Fin 64) (s0 s1 s2 : Fin 32)
    (hA : hyps8n n s0.val s1.val s2.val = true) (hp : loc8cond n s0.val s1.val s2.val = true) :
    badSix' n s0.val s1.val s2.val = true := by
  simp only [loc8cond, hA, Bool.false_or] at hp
  exact hp

/-- **THE COUNTING STEP OF THE EIGHT-VERTEX TRIANGLE CASE.**

Three vertices of a triangle, each **bad** (`G[X + {t}]` is not bipartite), each neighbour set
meeting both colour classes of a proper two-colouring of the residue `X = {0,1} + {2,3,4}` (with
`G[X]` inside `K_{2,3}`, carried by the six cells `A`), and the three neighbour sets with empty
triple intersection -- then **one of the three six-element subsets** `T + {0,1,2}`, `T + {0,1,3}`,
`T + {0,1,4}` **contains no independent triple**.

Erdős's hypothesis with `k = 1`, read on a six-element subset `W`, forces an independent set of size
`(6 - 1) / 2` rounded up, i.e. `3`, so this contradicts `LocIndep 1` as soon as the graph has been
carried into the language.

Note that the seven-vertex conclusion of `JSP90.loc7_lemma` ("some vertex of the eight is avoided by
no independent triple") is **false** here -- `23 976` counterexamples,
`discovery/JSP-000090/r167b.c` -- so this is not a routine port of that lemma: the five-point residue
needs the six-element subset, and only the *full* hypothesis of `LocIndep 1` provides it.

The statement is closed by `decide` sixty-four times, once for each of the `2 ^ 6` configurations of
the six cells of `G[X]` (`JSP90.loc8_piece_0 … 63`, four per file in `TriFiveA` … `TriFiveP`), which
is what keeps the kernel elaboration inside this machine's memory budget. -/
theorem loc8_lemma : ∀ (A : Fin 64) (s0 s1 s2 : Fin 32), hyps8n A s0.val s1.val s2.val = true →
    badSix' A s0.val s1.val s2.val = true := by
  intro A s0 s1 s2 hA
  fin_cases A
  · exact loc8_read _ _ _ _ hA (loc8_piece_0 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_1 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_2 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_3 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_4 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_5 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_6 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_7 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_8 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_9 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_10 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_11 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_12 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_13 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_14 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_15 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_16 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_17 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_18 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_19 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_20 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_21 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_22 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_23 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_24 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_25 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_26 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_27 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_28 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_29 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_30 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_31 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_32 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_33 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_34 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_35 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_36 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_37 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_38 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_39 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_40 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_41 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_42 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_43 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_44 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_45 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_46 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_47 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_48 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_49 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_50 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_51 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_52 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_53 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_54 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_55 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_56 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_57 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_58 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_59 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_60 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_61 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_62 s0 s1 s2)
  · exact loc8_read _ _ _ _ hA (loc8_piece_63 s0 s1 s2)

end JSP90
