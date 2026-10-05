import JSPProblem.TriFiveJ

/-!
# `JSPProblem/TriFiveK.lean` (round 167) -- pieces 40 … 43 of `JSP90.loc8_lemma`

The counting step of the eight-vertex triangle case: `A = 40 … 43` are the `2 ^ 6`
configurations of the six cells of the `K_{2,3}` residue, and for each of them no triple of
neighbour masks is a counterexample.  Sixteen `decide` pieces per file would need about `8 GB`
(measured), so the sixty-four are spread over sixteen files of **four**, chained
(`TriFiveJ` → this one) so that `lake build` elaborates them one at a time -- the lesson of
round 164, where the Fin 7 table had to be split for the same reason.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

theorem loc8_piece_40 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨40, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_41 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨41, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_42 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨42, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_43 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨43, by decide⟩ s0.val s1.val s2.val = true := by
  decide


end JSP90
