/-
# JSP-000090 — odd cycles and the odd-cycle characterisation of bipartiteness

This file develops the graph-theoretic machinery that JSP-000090 (Erdős Problem #73) needs, and
which Mathlib does not currently provide.  (At the pinned Mathlib revision `5ed29652`, the header of
`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` lists as an open `TODO`:

> Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.

`TODO`.)

Contents:

* `walk_length_parity_congr`, `walk_length_parity_ne` — walks with the same endpoints have the same
  length parity in a graph with no odd closed walk;
* `colorable_two_of_even_closed_walks` — a graph all of whose closed walks has even length carries a
  proper `2`-colouring, i.e. is bipartite.  This is one direction of the TODO;
* `exists_odd_closed_walk_of_not_bipartite`;
* `exists_odd_cycle_inj` — an odd closed walk contains a *simple* odd cycle, formalised as an
  injective map `f : Fin m → V` with `m` odd, `m ≥ 3`, such that `f i` is adjacent to the cyclic
  successor `f (cycSucc i)`;
* `indep_card_le_of_odd_cycle` — an independent set meeting such a cycle has at most `(m - 1) / 2`
  vertices: the standard fact `α(C_n) ≤ ⌊n / 2⌋`;
* `locIndep_zero_isBipartite` — **the complete `k = 0` case of Erdős Problem #73**: if every vertex
  set of `G` carries an independent set of size `≥ |X| / 2`, then `G` is bipartite;
* `erdős73_zero` — hence `Erdős73 0`, i.e. Erdős Problem #73 itself holds for the parameter
  `k = 0`, with the sharp constant `m = 0`.
-/

import JSPProblem.Reed
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace JSP90

open Finset Fintype Set
open SimpleGraph (Walk)

variable {V : Type*}

/-! ### Parity of walks -/

section Parity

variable {G : SimpleGraph V}

/-- **Walks with the same endpoints have the same length parity.**
If every closed walk of `G` that starts in `S` has even length, then two walks `p, q : G.Walk a b`
with `a ∈ S` satisfy `p.length % 2 = q.length % 2`. -/
theorem walk_length_parity_congr {S : Set V}
    (hS : ∀ x ∈ S, ∀ r : G.Walk x x, r.length % 2 = 0)
    {a b : V} (ha : a ∈ S) (p q : G.Walk a b) : p.length % 2 = q.length % 2 := by
  have hh := hS a ha (p.append q.reverse)
  rw [Walk.length_append, Walk.length_reverse] at hh
  omega

/-- Two walks `a → b` and `a → c` across an edge `b ~ c` differ in parity. -/
theorem walk_length_parity_ne {S : Set V}
    (hS : ∀ x ∈ S, ∀ r : G.Walk x x, r.length % 2 = 0)
    {a b c : V} (ha : a ∈ S) (hadj : G.Adj b c) (p : G.Walk a b) (q : G.Walk a c) :
    p.length % 2 ≠ q.length % 2 := by
  intro he
  have h1 := walk_length_parity_congr hS ha (p.append (Walk.cons hadj Walk.nil)) q
  rw [Walk.length_append, Walk.length_cons] at h1
  have hmod : (p.length + 1) % 2 ≠ p.length % 2 := by omega
  rw [← he] at h1
  exact hmod h1

/-- A graph in which every closed walk of `W` has even length restricts to a proper `2`-colouring on
`W`: there is `d : V → Fin 2` separating the endpoints of every edge inside `W`. -/
theorem col_of_even_closed_walks [Fintype V] :
    ∀ (k : ℕ) (W : Set V), W.ncard = k →
      (∀ w ∈ W, ∀ p : G.Walk w w, p.length % 2 = 0) →
      ∃ d : V → Fin 2, ∀ ⦃x y : V⦄, x ∈ W → y ∈ W → G.Adj x y → d x ≠ d y := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro W hcard hW
    by_cases hW0 : W = ∅
    · obtain rfl := hW0
      refine ⟨fun _ => (0 : Fin 2), fun x y hx hy hadj => ?_⟩
      exact (Set.mem_empty_iff_false (α := V) (x := x)).mpr hx |>.elim
    obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hW0
    set W' : Set V := W \ {z | G.Reachable b z} with hW'def
    have hmemW' : ∀ z ∈ W, ¬ G.Reachable b z → z ∈ W' := by
      intro z hz hz'
      rw [hW'def, Set.mem_sdiff]
      exact ⟨hz, hz'⟩
    have hbW' : b ∉ W' := by
      rw [hW'def, Set.mem_sdiff]
      exact fun h => h.2 (Set.mem_ofPred (p := G.Reachable b) |>.mpr ⟨Walk.nil⟩)
    have hsubW' : W' ⊆ W := by
      intro a ha
      rw [hW'def] at ha
      exact ha.1
    have hle : W'.ncard < W.ncard := Set.ncard_lt_ncard ⟨hsubW', fun h => hbW' (h hb)⟩
    have hWn : W'.ncard < k := hle.trans_eq hcard
    obtain ⟨c', hc'⟩ := ih W'.ncard hWn W' rfl (fun z hz p => hW z hz.1 p)
    have hreach_adj : ∀ {z y : V}, G.Adj z y → G.Reachable b z → G.Reachable b y := by
      intro z y hadj hz
      exact SimpleGraph.Reachable.trans hz (SimpleGraph.Reachable.symm
        (SimpleGraph.adj_le_reachable G y z hadj.symm))
    have hmod : ∀ m : ℕ, (m + 1) % 2 ≠ m % 2 := by omega
    -- across an edge the parity of walks from `b` flips, so both cannot be even
    have key : ∀ {v w : V}, G.Adj v w → (∃ r : G.Walk b v, r.length % 2 = 0) →
        ¬ ∃ r : G.Walk b w, r.length % 2 = 0 := by
      intro v w hadj h0 h0'
      obtain ⟨p, hp⟩ := h0
      obtain ⟨q, hq⟩ := h0'
      have h1 := walk_length_parity_congr (fun x hx r => hW x hx r) hb
        (p.append (Walk.cons hadj Walk.nil)) q
      rw [Walk.length_append, Walk.length_cons, Walk.length_nil, Nat.zero_add] at h1
      exact absurd (h1.trans hq) fun heq => (hmod p.length) (heq.trans hp.symm)
    refine ⟨fun x => if hx : G.Reachable b x then
        (if ∃ r : G.Walk b x, r.length % 2 = 0 then (0 : Fin 2) else 1) else c' x, ?_⟩
    intro x y hxW hyW hadj
    by_cases hxr : G.Reachable b x
    · have hyr : G.Reachable b y := hreach_adj hadj hxr
      by_cases hex : (∃ r : G.Walk b x, r.length % 2 = 0)
      · simp only [dif_pos hxr, dif_pos hyr, if_pos hex, if_neg (key hadj hex)]
        exact fun h => absurd (congrArg Fin.val h) (by omega)
      · have hey : (∃ r : G.Walk b y, r.length % 2 = 0) := by
          by_contra hc
          push_neg at hc
          obtain ⟨q0⟩ := hyr
          refine hex ⟨q0.append (Walk.cons hadj.symm Walk.nil), ?_⟩
          rw [Walk.length_append, Walk.length_cons, Walk.length_nil, Nat.zero_add]
          rcases Nat.mod_two_eq_zero_or_one q0.length with hzero | hone
          · exact absurd hzero (hc q0)
          · omega
        simp only [dif_pos hxr, dif_pos hyr, if_neg hex, if_pos hey]
        exact fun h => absurd (congrArg Fin.val h) (by omega)
    · have hyn : ¬ G.Reachable b y := fun h => hxr (hreach_adj hadj.symm h)
      simp only [dif_neg hxr, dif_neg hyn]
      exact hc' (hmemW' _ hxW hxr) (hmemW' _ hyW hyn) hadj

/-- **A graph whose closed walks all have even length is bipartite.** -/
theorem colorable_two_of_even_closed_walks [Fintype V]
    (hall : ∀ (x : V) (p : G.Walk x x), p.length % 2 = 0) : G.Colorable 2 := by
  obtain ⟨d, hd⟩ := col_of_even_closed_walks Set.univ.ncard Set.univ rfl (fun x _ p => hall x p)
  exact ⟨SimpleGraph.Coloring.mk d (fun hadj => hd (Set.mem_univ _) (Set.mem_univ _) hadj)⟩

/-- **A non-bipartite graph has an odd closed walk.** -/
theorem exists_odd_closed_walk_of_not_bipartite [Fintype V] (h : ¬ G.Colorable 2) :
    ∃ (w : V) (p : G.Walk w w), p.length % 2 = 1 := by
  by_contra hc
  have hall : ∀ (w : V) (p : G.Walk w w), p.length % 2 = 0 := by
    intro w p
    rcases Nat.mod_two_eq_zero_or_one p.length with h | h
    · exact h
    · exact absurd h (fun h' => hc ⟨w, p, h'⟩)
  exact h ⟨(colorable_two_of_even_closed_walks hall).some⟩


/-! ### The cyclic successor on `Fin n` -/

section Cyc

/-- The cyclic successor on `Fin n` (for `i = n - 1` it wraps around to `0`). -/
def cycSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.2)⟩

@[simp] theorem cycSucc_val {n : ℕ} (i : Fin n) : (cycSucc i).val = (i.val + 1) % n := rfl

theorem cycSucc_ne {n : ℕ} (i : Fin n) (hn : 2 ≤ n) : cycSucc i ≠ i := by
  have hlt : i.val < n := i.2
  intro he
  have hv : (i.val + 1) % n = i.val := by simpa using congrArg Fin.val he
  by_cases hc : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hc] at hv
    omega
  · have h1 : i.val + 1 = n := by omega
    rw [h1, Nat.mod_self] at hv
    omega

theorem cycSucc_injective {n : ℕ} (i j : Fin n) (h : cycSucc i = cycSucc j) : i = j := by
  have hv : (i.val + 1) % n = (j.val + 1) % n := by simpa using congrArg Fin.val h
  have hli : i.val < n := i.2
  have hlj : j.val < n := j.2
  by_cases hi1 : i.val + 1 = n
  · by_cases hj1 : j.val + 1 = n
    · exact Fin.ext (by omega)
    · have hj2 : j.val + 1 < n := by omega
      rw [hi1, Nat.mod_self, Nat.mod_eq_of_lt hj2] at hv
      omega
  · have hi2 : i.val + 1 < n := by omega
    by_cases hj1 : j.val + 1 = n
    · rw [Nat.mod_eq_of_lt hi2, hj1, Nat.mod_self] at hv
      omega
    · have hj2 : j.val + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hi2, Nat.mod_eq_of_lt hj2] at hv
      omega

end Cyc

/-! ### Simple walks -/

section Simple

variable {G : SimpleGraph V}

/-- The first vertex of the support of a walk. -/
theorem Walk.support_get_zero (q : G.Walk a b) (h : (0 : ℕ) < q.support.length) :
    q.support.get ⟨0, h⟩ = a := by
  cases q <;> rfl

/-- Adjacency of two consecutive entries of a chain. -/
theorem isChain_rel_getElem {l : List V} (h : l.IsChain G.Adj) {i : ℕ} (hi : i + 1 < l.length) :
    G.Adj (l[i]) (l[i + 1]) := List.isChain_iff_getElem.mp h i hi

/-- **Splicing an odd closed walk.**  If a closed walk of odd length `L` visits some vertex twice,
at positions `i < j < L`, then it contains an odd closed walk of strictly smaller length. -/
theorem exists_shorter_odd_walk {G : SimpleGraph V} {v w : V} (p : G.Walk v w) (hvw : v = w)
    (hlen : p.length = L) (hop : L % 2 = 1) {i j : ℕ} (hii : 0 < i) (hij : i < j)
    (hjl : j ≤ L) (hrep : p.getVert i = p.getVert j) :
    ∃ (x y : V) (w : G.Walk x y), x = y ∧ w.length % 2 = 1 ∧ w.length < L := by
  subst hvw
  have hidx : i + (j - i) = j := by omega
  have hleA : j - i ≤ L - i := by omega
  have hlenA : ((p.drop i).take (j - i)).length = j - i := by
    rw [Walk.take_length, Walk.drop_length, hlen, Nat.min_eq_left hleA]
  have hleB : i ≤ L := by omega
  have hlenB : ((p.drop j).append (p.take i)).length = L - j + i := by
    rw [Walk.length_append, Walk.drop_length, Walk.take_length, hlen, Nat.min_eq_left hleB]
  have hA : j - i < L := by
    have := Nat.sub_le j i
    omega
  have hB : L - j + i < L :=
    lt_of_lt_of_eq (Nat.add_lt_add_left hij (L - j)) (Nat.sub_add_cancel hjl)
  by_cases hAj : (j - i) % 2 = 1
  · refine ⟨p.getVert i, (p.drop i).getVert (j - i), (p.drop i).take (j - i), ?_, ?_, ?_⟩
    · rw [Walk.drop_getVert, hidx]; exact hrep
    · rw [hlenA, hAj]
    · rw [hlenA]; exact hA
  · have ha0 : (j - i) % 2 = 0 := Nat.mod_two_eq_zero_or_one (j - i) |>.resolve_right hAj
    have hsum : j - i + (L - j + i) = L := by omega
    refine ⟨p.getVert j, p.getVert i, (p.drop j).append (p.take i), hrep.symm, ?_, ?_⟩
    · rw [hlenB]; omega
    · rw [hlenB]; exact hB

/-- **An odd closed walk contains a simple odd cycle.**
Formally: there are `m ≥ 3` (odd) vertices and an injective `f : Fin m → V` with `f i` adjacent to
`f (cycSucc i)`. -/
theorem exists_odd_cycle_inj {G : SimpleGraph V} :
    ∀ (L : ℕ) (v w : V) (p : G.Walk v w), v = w → p.length = L → L % 2 = 1 →
      ∃ (m : ℕ) (f : Fin m → V), m % 2 = 1 ∧ 3 ≤ m ∧ Function.Injective f ∧
        ∀ i : Fin m, G.Adj (f i) (f (cycSucc i)) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro v w p hvw hlen hop
    have hne0 : L ≠ 0 := by omega
    have hL3 : 3 ≤ L := by
      have hL1 : L ≠ 1 := by
        intro h
        have h1' : G.Adj v w := Walk.adj_of_length_eq_one (p := p) (by omega)
        exact G.loopless.irrefl v (hvw.symm ▸ h1')
      omega
    have hne0p : p.length ≠ 0 := by omega
    obtain ⟨u, h, q, hp⟩ := Walk.not_nil_iff.mp
      (fun hn => hne0p (hlen ▸ Walk.length_eq_zero_iff.mpr hn))
    rw [hp] at hlen
    have hlen' : q.length + 1 = L := (Walk.length_cons h q).symm.trans hlen
    have hclen : q.support.length = q.length + 1 := Walk.length_support q
    have hchain : q.support.IsChain G.Adj := Walk.isChain_adj_support q
    have hlast : q.support.get ⟨q.length, by omega⟩ = w := by
      rw [List.get_eq_getElem, ← Walk.getVert_eq_support_getElem q (le_refl _),
        Walk.getVert_length]
    have hfirst : q.support.get ⟨0, by omega⟩ = u := Walk.support_get_zero q _
    have hclose : G.Adj (q.support[q.length]) (q.support[0]) := by
      show G.Adj (q.support.get ⟨q.length, _⟩) (q.support.get ⟨0, _⟩)
      rw [hlast, hfirst]; exact hvw ▸ h
    have h1 : ∀ (t : Fin q.support.length), t.val < q.length →
        (Walk.cons h q).getVert (t.val + 1) = q.support.get t := by
      intro t ht
      have hA : (Walk.cons h q).getVert (t.val + 1) = q.getVert t.val := by
        simpa using (Walk.getVert_cons_succ q h (n := t.val))
      have hB : q.getVert t.val = q.support[t.val] :=
        Walk.getVert_eq_support_getElem q (Nat.le_of_lt ht)
      have hC : q.support[t.val] = q.support.get t := by
        show q.support[t.val] = q.support.get ⟨t.val, _⟩
        rw [(@List.get_eq_getElem V q.support t)]
      exact hA.trans (hB.trans hC)
    have splice : ∀ (i j : Fin q.support.length), i.val < j.val → j.val < q.length →
        q.support.get i = q.support.get j →
        ∃ (m : ℕ) (f : Fin m → V), m % 2 = 1 ∧ 3 ≤ m ∧ Function.Injective f ∧
          ∀ k : Fin m, G.Adj (f k) (f (cycSucc k)) := by
      intro i j hij hjl hEq
      have hj' := j.isLt
      have hjL : j.val + 1 ≤ L := by omega
      have hil : i.val < q.length := by omega
      obtain ⟨x, y, w', hxy, hwmod, hwlt⟩ :=
        exists_shorter_odd_walk (i := i.val + 1) (j := j.val + 1) (Walk.cons h q) hvw hlen hop
          (by omega) (by omega) hjL (Eq.trans (h1 i hil) (Eq.trans hEq (h1 j hjl).symm))
      exact ih w'.length hwlt x y w' hxy rfl hwmod
    by_cases hcoll : ∃ (i j : Fin q.support.length),
        i.val < j.val ∧ q.support[i.val] = q.support[j.val]
    · obtain ⟨i, j, hlt, heq⟩ := hcoll
      have hj' := j.isLt
      have hi' := i.isLt
      have hil : i.val < q.length := by omega
      have hq : q.length < q.support.length := by rw [hclen]; omega
      have hgetL : (Walk.cons h q).getVert L = q.support.get ⟨q.length, hq⟩ :=
        by rw [← hlen, Walk.getVert_length]; exact hlast.symm
      have heqj : q.support.get i = q.support.get j := by
        show q.support[i.val] = q.support[j.val]
        exact heq
      rcases Nat.lt_or_ge j.val q.length with hjl' | hjl'
      · obtain ⟨x, y, w', hxy, hwmod, hwlt⟩ :=
          exists_shorter_odd_walk (i := i.val + 1) (j := j.val + 1) (Walk.cons h q) hvw hlen hop
            (by omega) (by omega) (by omega)
            (Eq.trans (h1 i hil) (Eq.trans heqj (h1 j hjl').symm))
        exact ih w'.length hwlt x y w' hxy rfl hwmod
      · have hjeq : j.val = q.length := by omega
        have hjeq' : q.support.get i = q.support.get ⟨q.length, hq⟩ := by
          show q.support[i.val] = q.support[q.length]
          simpa only [hjeq] using heq
        obtain ⟨x, y, w', hxy, hwmod, hwlt⟩ :=
          exists_shorter_odd_walk (i := i.val + 1) (j := L) (Walk.cons h q) hvw hlen hop
            (by omega) (by omega) le_rfl (Eq.trans (h1 i hil) (Eq.trans hjeq' hgetL.symm))
        exact ih w'.length hwlt x y w' hxy rfl hwmod
    · refine ⟨q.support.length, fun t : Fin q.support.length => q.support[t.val], ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · intro i j hij
        by_contra hc
        rcases lt_or_gt_of_ne hc with hlt | hgt
        · exact hcoll ⟨i, j, hlt, hij⟩
        · exact hcoll ⟨j, i, hgt, hij.symm⟩
      · intro i
        have hi' := i.isLt
        by_cases hi : i.val + 1 < q.support.length
        · have hcv : (cycSucc i).val = i.val + 1 := by
            rw [cycSucc_val]; exact Nat.mod_eq_of_lt hi
          have hadj := isChain_rel_getElem hchain (i := i.val) hi
          show G.Adj (q.support[i.val]) (q.support[(cycSucc i).val])
          simpa only [hcv] using hadj
        · have hi2 : i.val + 1 = q.support.length := by omega
          have hi3 : i.val = q.length := by
            have := hclen
            omega
          have hcv : (cycSucc i).val = 0 := by
            rw [cycSucc_val, hi2]; exact Nat.mod_self _
          show G.Adj (q.support[i.val]) (q.support[(cycSucc i).val])
          simpa only [hi3, hcv] using hclose

end Simple

/-! ### Independent sets on an odd cycle -/

section Indep

variable {G : SimpleGraph V}

/-- **An odd cycle meets an independent set in at most half of its vertices, rounded down.**
Let `m` be odd, let `f : Fin m → V` be injective with `f i` adjacent to the cyclic successor
`f (cycSucc i)`, and let `S` be an independent set consisting of vertices of the cycle, i.e.
`∀ x ∈ S, x = f i` for some `i`.  Then `2 * |S| + 1 ≤ m`, i.e. `|S| ≤ ⌊m / 2⌋ = (m - 1) / 2`.

This is the classical bound `α(C_m) ≤ ⌊m / 2⌋`, proved combinatorially: the cyclic successor maps
every vertex of the cycle lying in `S` to a vertex of the cycle lying outside `S` (the two are
adjacent, hence distinct), so `S` is no larger than the complement of itself inside the cycle. -/
theorem indep_card_le_of_odd_cycle {m : ℕ} (hm : m % 2 = 1) (f : Fin m → V)
    (hinj : Function.Injective f) (hcyc : ∀ i : Fin m, G.Adj (f i) (f (cycSucc i)))
    (S : Finset V) (hS : G.IsIndepSet S)
    (hSin : ∀ ⦃x : V⦄, x ∈ S → ∃ i : Fin m, f i = x) :
    2 * S.card + 1 ≤ m := by
  classical
  -- `T` = the vertices of the cycle lying in `S`, `U` = the vertices of the cycle outside `S`
  have hle1 : ((Finset.univ.filter fun i : Fin m => f i ∈ S).image fun i : Fin m => cycSucc i).card
      ≤ (Finset.univ.filter fun i : Fin m => f i ∉ S).card := by
    refine Finset.card_le_card ?_
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hiS : f i ∈ S := (Finset.mem_filter.mp hi).2
    have hne : f i ≠ f (cycSucc i) := fun h => G.loopless.irrefl _ (h.symm ▸ hcyc i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hmemS => hS hiS hmemS hne (hcyc i)⟩
  have hle2 : ((Finset.univ.filter fun i : Fin m => f i ∈ S).image fun i : Fin m => cycSucc i).card
      = (Finset.univ.filter fun i : Fin m => f i ∈ S).card :=
    Finset.card_image_of_injective _ (fun i j h => cycSucc_injective i j h)
  have hTUcard : (Finset.univ.filter fun i : Fin m => f i ∈ S).card
      ≤ (Finset.univ.filter fun i : Fin m => f i ∉ S).card := by
    rw [← hle2]
    exact hle1
  have hsplit : (Finset.univ.filter fun i : Fin m => f i ∈ S).card
      + (Finset.univ.filter fun i : Fin m => f i ∉ S).card = m := by
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i : Fin m => f i ∉ S)
    have h3 : (Finset.univ.filter fun i : Fin m => ¬ (f i ∉ S))
        = Finset.univ.filter fun i : Fin m => f i ∈ S := by
      ext i
      simp
    have h3card := congrArg Finset.card h3
    have h4 : ((Finset.univ : Finset (Fin m)).card) = m := by simp
    omega
  have hTS : (Finset.univ.filter fun i : Fin m => f i ∈ S).card = S.card := by
    have heq : S = (Finset.univ.filter fun i : Fin m => f i ∈ S).image f := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hix⟩ := hSin hx
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hix ▸ hx⟩, hix⟩
      · intro hx
        obtain ⟨i, hi, hif⟩ := Finset.mem_image.mp hx
        exact hif ▸ (Finset.mem_filter.mp hi).2
    calc (Finset.univ.filter fun i : Fin m => f i ∈ S).card
        = ((Finset.univ.filter fun i : Fin m => f i ∈ S).image f).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ = S.card := congrArg Finset.card heq.symm
  have hlt : 2 * (Finset.univ.filter fun i : Fin m => f i ∈ S).card < m := by omega
  omega

/-- **Erdős's local hypothesis with `k = 0` forces bipartiteness.**
If every vertex set `X` of `G` carries an independent set `S ⊆ X` with `2 * |S| ≥ |X|`, then `G`
is bipartite.  Indeed a non-bipartite graph contains an odd cycle, while an independent set
inside such a cycle has at most `(|C| - 1) / 2` vertices, i.e. `2 * |S| + 1 ≤ |C|`, contradicting
`2 * |S| ≥ |C|`.

This closes the `k = 0` instance of Erdős Problem #73, and it uses an odd-cycle characterisation
of bipartiteness that Mathlib lists as an open `TODO`
(`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`): `JSPProblem/OddCycle.lean` proves it from
scratch, on top of `SimpleGraph.Walk`. -/
theorem locIndep_zero_isBipartite [Fintype V] {G : SimpleGraph V} (h : LocIndep 0 G) :
    G.IsBipartite := by
  classical
  by_contra hb
  obtain ⟨w, p, hmod⟩ := exists_odd_closed_walk_of_not_bipartite (G := G) hb
  obtain ⟨m, f, hm, hm3, hinj, hcyc⟩ :=
    exists_odd_cycle_inj (G := G) p.length w w p rfl rfl hmod
  have hcard : (Finset.image f (Finset.univ : Finset (Fin m))).card = m := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin m)) hinj]
    simp
  obtain ⟨S, hS, hSi, hbnd⟩ := h (Finset.image f (Finset.univ : Finset (Fin m)))
  have hSin : ∀ ⦃x : V⦄, x ∈ S → ∃ i : Fin m, f i = x := by
    intro x hx
    obtain ⟨i, _, hix⟩ := Finset.mem_image.mp (hS hx)
    exact ⟨i, hix⟩
  have hle := indep_card_le_of_odd_cycle hm f hinj hcyc S hSi hSin
  omega

/-- **Erdős Problem #73 for `k = 0`, with the sharp constant `m = 0`.**
A graph in which every vertex set carries an independent set of size at least `|X| / 2` is
bipartite: it is the union of a bipartite graph and *zero* extra vertices. -/
theorem erdos73On_zero : Erdős73On 0 0 := by
  intro W instW G hG
  exact isBipartite_closeToBipartite (m := 0) (locIndep_zero_isBipartite (V := W) hG)

/-- **Erdős Problem #73 holds for `k = 0`.**  The hard direction of Erdős Problem #73 is proved
for the parameter `k = 0`; the remaining case `k ≥ 1` is Reed's theorem proper. -/
theorem erdos73_zero : Erdős73 0 := ⟨0, erdos73On_zero⟩

end Indep

end Parity

end JSP90
