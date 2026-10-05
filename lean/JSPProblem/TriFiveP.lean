import JSPProblem.TriFiveO

/-!
# `JSPProblem/TriFiveP.lean` (round 167) -- pieces 60 … 63 of `JSP90.loc8_lemma`

The counting step of the eight-vertex triangle case: `A = 60 … 63` are the `2 ^ 6`
configurations of the six cells of the `K_{2,3}` residue, and for each of them no triple of
neighbour masks is a counterexample.  Sixteen `decide` pieces per file would need about `8 GB`
(measured), so the sixty-four are spread over sixteen files of **four**, chained
(`TriFiveO` → this one) so that `lake build` elaborates them one at a time -- the lesson of
round 164, where the Fin 7 table had to be split for the same reason.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

set_option maxRecDepth 100000

theorem loc8_piece_60 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨60, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_61 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨61, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_62 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨62, by decide⟩ s0.val s1.val s2.val = true := by
  decide

theorem loc8_piece_63 : ∀ (s0 s1 s2 : Fin 32),
    loc8cond ⟨63, by decide⟩ s0.val s1.val s2.val = true := by
  decide


end JSP90
