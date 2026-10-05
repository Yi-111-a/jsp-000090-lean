import JSPProblem.TriFiveK

/-!
# `JSPProblem/TriFiveL.lean` (round 167) -- pieces 44 … 47 of `JSP90.loc8_lemma`

The counting step of the eight-vertex triangle case: `A = 44 … 47` are the `2 ^ 6`
configurations of the six cells of the `K_{2,3}` residue, and for each of them no triple of
neighbour masks is a counterexample.  Sixteen `decide` pieces per file would need about `8 GB`
(measured), so the sixty-four are spread over sixteen files of **four**, chained
(`TriFiveK` → this one) so that `lake build` elaborates them one at a time -- the lesson of
round 164, where the Fin 7 table had to be split for the same reason.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

theorem loc8_piece_44 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨44, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_45 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨45, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_46 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨46, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_47 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨47, by decide⟩ s0.val s1.val s2.val = true := by
  decide


end JSP90
