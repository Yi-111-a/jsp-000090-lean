import JSPProblem.ThreeB
namespace JSP90
open Finset Fintype Set SimpleGraph
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
noncomputable section
local instance thD (G : SimpleGraph V) : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
local instance thE : DecidableEq V := Classical.decEq V

example {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    {f : Fin 5 → V} (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {w1 w2 : V} (hA : IsShapeA G C D w1 w2) :
    ∃ a₁ b₁ c₁ d₁ e₁ : V, RingShapeAData G C D f w1 w2 a₁ b₁ c₁ d₁ e₁ := by
  obtain ⟨g, hg, hcycg, hmemg, a₁, b₁, c₁, d₁, e₁, hdata1⟩ :=
    exists_ringShapeA hC hshort hC5 f hf hcyc hmem hA
  obtain ⟨-, -, hdist, hshape, hmissed⟩ := hdata1
  obtain ⟨hDset, hab, hbc, hcw1, hw2a, hw1w2⟩ := hshape
  obtain ⟨hsdiff, hde, had, hce⟩ := hmissed
  obtain ⟨ha, hb, hc, hw1, hw2, hw, hab', hbc', hac'⟩ := hdist
  exact ⟨a₁, b₁, c₁, d₁, e₁, ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, ha, hb, hc, hw1, hw2, hw,
    hab', hbc', hac', hDset, hab, hbc, hcw1, hw2a, hw1w2, hsdiff, hde, had, hce⟩⟩
end
end JSP90
