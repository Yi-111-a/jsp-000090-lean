import JSPProblem.TriFiveN

/-!
# `JSPProblem/TriFiveO.lean` (round 167) -- pieces 56 … 59 of `JSP90.loc8_lemma`

The counting step of the eight-vertex triangle case: `A = 56 … 59` are the `2 ^ 6`
configurations of the six cells of the `K_{2,3}` residue, and for each of them no triple of
neighbour masks is a counterexample.  Sixteen `decide` pieces per file would need about `8 GB`
(measured), so the sixty-four are spread over sixteen files of **four**, chained
(`TriFiveN` → this one) so that `lake build` elaborates them one at a time -- the lesson of
round 164, where the Fin 7 table had to be split for the same reason.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

theorem loc8_piece_56 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨56, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_57 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨57, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_58 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨58, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_59 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨59, by decide⟩ s0.val s1.val s2.val = true := by
  decide


end JSP90
