import JSPProblem.Cut
namespace JSP90
open Finset Fintype Set
universe u
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {T : Finset V}
#check @SimpleGraph.reachable_iff_reflTransGen
#check @SimpleGraph.reachable_eq_reflTransGen
example {u x : V} (h : (deleteFinset G T).Reachable u x) :
    Relation.ReflTransGen (deleteFinset G T).Adj u x :=
  h ▸ SimpleGraph.reachable_eq_reflTransGen
example {C : Finset V} (hC : G.IsClique C) :
    ∀ (s : Finset V), (induceFinset G s).IsClique C := by
  intro s v hv w hw hne
  exact hC hv hw hne
end JSP90
