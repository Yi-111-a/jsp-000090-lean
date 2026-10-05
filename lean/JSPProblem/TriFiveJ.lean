import JSPProblem.TriFiveI

/-!
# `JSPProblem/TriFiveJ.lean` (round 167) -- pieces 36 … 39 of `JSP90.loc8_lemma`

The counting step of the eight-vertex triangle case: `A = 36 … 39` are the `2 ^ 6`
configurations of the six cells of the `K_{2,3}` residue, and for each of them no triple of
neighbour masks is a counterexample.  Sixteen `decide` pieces per file would need about `8 GB`
(measured), so the sixty-four are spread over sixteen files of **four**, chained
(`TriFiveI` → this one) so that `lake build` elaborates them one at a time -- the lesson of
round 164, where the Fin 7 table had to be split for the same reason.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

theorem loc8_piece_36 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨36, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_37 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨37, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_38 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨38, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_39 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨39, by decide⟩ s0.val s1.val s2.val = true := by
  decide


end JSP90
