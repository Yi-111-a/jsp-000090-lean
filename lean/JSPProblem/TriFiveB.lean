import JSPProblem.TriFiveA

/-!
# `JSPProblem/TriFiveB.lean` (round 167) -- pieces 4 … 7 of `JSP90.loc8_lemma`

The counting step of the eight-vertex triangle case: `A = 4 … 7` are the `2 ^ 6`
configurations of the six cells of the `K_{2,3}` residue, and for each of them no triple of
neighbour masks is a counterexample.  Sixteen `decide` pieces per file would need about `8 GB`
(measured), so the sixty-four are spread over sixteen files of **four**, chained
(`TriFiveA` → this one) so that `lake build` elaborates them one at a time -- the lesson of
round 164, where the Fin 7 table had to be split for the same reason.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

theorem loc8_piece_4 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨4, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_5 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨5, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_6 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨6, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_7 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨7, by decide⟩ s0.val s1.val s2.val = true := by
  decide


end JSP90
