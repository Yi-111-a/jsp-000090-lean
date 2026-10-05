import JSPProblem.TriCount

/-!
# JSP-000090, round 166 — `JSPProblem/TriFix.lean`: **THE TRANSFER, AND THE SEVEN-VERTEX AXIS WITH THE
## OPTIMAL CONSTANT `2`**

Attack family 87.  This file executes the single remaining gap recorded by round 165
(`policy.json`, "THE TRANSFER"): it carries a graph into the `Fin 7` language of
`lean/JSPProblem/TriCount.lean` and closes

* `JSP90.triCase` — **MISSING LEMMA 1**, the triangle case of the seven-vertex axis;
* `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` — `LocIndep 1 → |V| ≤ 7 ⟹
  CloseToBipartite 2 G`, i.e. **Erdős #73 at `k = 1` on seven vertices with the optimal constant
  `2`**, and the downstream chain in the `Erdős73On`, transversal and piece shapes, plus the
  optimality of the constant (`JSP90.tauOdd_sun3`, `JSP90.not_locIndepOneAllSmallOrder_one_of_card_le_seven`).

The bridge between the two (the residue of *every* triangle is bipartite, so `JSP90.triCase` needs no
extra hypothesis) was already proved in round 150 as
`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven`
(`lean/JSPProblem/Seven.lean`), and this file uses it; Part 2 re-proves the counting it rests on in
reusable form (`JSP90.card_inter_le_one_of_isNClique_three_indep`).

## The transfer, part by part

Write `X = V \ T` for the residue of the triangle `T = {a, b, c}`, `S_t = N(t) ∩ X`, and suppose all
three vertices of `T` are **bad** (`G[X + {t}]` not bipartite).  `JSP90.card_cls_ge_two`
(`TriCount.lean`) then forces `|X| = 4` with `|P| = |Q| = 2` for the two colour classes `P`, `Q` of a
proper two-colouring `d` of `G[X]`, and this file builds

* `xpt : Fin 4 → V` — the four points of `X`, `0, 1` in `P` and `2, 3` in `Q`;
* `tpt : Fin 3 → V` — the three vertices of `T`;
* `inv : Fin 7 → V` — the bijection `i ↦ xpt ⟨i⟩` for `i < 4`, `tpt ⟨i − 4⟩` otherwise;
* `A : Fin 4 → Bool` — the four cells of `G[X]` (`JSP90.hcrossAll`),
* `S : Fin 3 → Fin 4 → Bool` — the three neighbour sets,

so that `adj7 A S i j = decide (G.Adj (inv i) (inv j))` (`JSP90.hadj7`, a `49`-case analysis).  The
three hypotheses of `JSP90.hyps` are then *transferred*:

* `JSP90.htri` — empty triple intersection (`JSP90.card_adjIn_le_two_of_isNClique_three`);
* `JSP90.hbi0`, `JSP90.hbi1` — each `S_t` meets both colour classes (`JSP90.exists_adjIn_color`);
* `JSP90.hbad8` — **each `t` is bad in the `Fin 7` language**, which is the delicate half: the
  hypothesis is `monoS S t m = true ∧ proper8 A m = true` for some colouring index `m : Fin 16`,
  and the conclusion is a genuine two-colouring of `deleteFinset G (T \ {t})`.  It is obtained from
  `JSP90.isBipartite_of_adjIn_mono`, with the colour of a residual point read off `col4 m` and
  properness read off by `JSP90.proper8_adj` (`proper8` really is properness — the correction round
  165 made).  The missing piece of that transfer, `JSP90.monoS_get` (reading monochromaticity
  *forward*), is proved here.

Finally Erdős's hypothesis, read on the six-element set `univ \ {inv z}`, produces an independent
triple avoiding `z`, i.e. `hasTripleAvoiding A S z = true`, contradicting
`JSP90.loc7_lemma`.

## Why this closes the axis

`JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase` (round 162) needs the triangle case for
*every* triangle, while `JSP90.triCase` is stated with a bipartite residue; round 150 supplied the
bridge.  A shortest odd cycle of `G` then has three, five or seven vertices, and the two long cases
were closed in round 162, so the seven-vertex axis — the last order at which the measured constant is
`2` (`discovery/JSP-000090/r144b_n8.log`: no `LocIndep 1` graph on eight vertices has `tauOdd ≥ 3`) —
is closed, and `JSP90.sun3` shows the constant `2` is optimal.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

local instance tcDecFix : DecidableEq V := Classical.decEq V

local instance tcAdjFix : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

/-! ## Part 0 — glue between the `Fin 7` language and the graph

`monoS S t m = true` says the colouring `col4 m` is constant on `S t`; `JSP90.monoS_get` is the
reading of that statement, and it is what the badness transfer consumes. -/

/-- A `Bool` colouring determines a two-colouring of `Fin 2`. -/
def bitCol : Bool → Fin 2 := fun b => if b = true then 1 else 0

@[simp] theorem bitCol_true : bitCol true = 1 := rfl

@[simp] theorem bitCol_false : bitCol false = 0 := rfl

theorem bitCol_inj : ∀ a b : Bool, bitCol a = bitCol b → a = b := by decide

/-- In `Fin 2`, two colours which differ are opposite. -/
theorem eq_opp2_of_ne' : ∀ (i j : Fin 2), i ≠ j → i = opp2 j := eq_opp2_of_ne

/-- **THE OPPOSITE COLOUR IS AN INVOLUTION.** -/
theorem opp2_involutive : ∀ i : Fin 2, opp2 (opp2 i) = i := by
  intro i
  exact ((eq_opp2_iff_ne (i := i) (j := opp2 i)).mpr (opp2_ne i).symm).symm

/-- **A THREE-FOLD DISJUNCTION OF `Bool`s, WITH THE FIRST TWO GONE.**  `Bool.or` short-circuits, so
`(a || b || c) = true` together with `a = b = false` reads back `c = true`.  This is the shape of the
six guarded pairs of `JSP90.monoS`. -/
theorem bool_or3_false {a b c : Bool} (h : (a || b || c) = true) (ha : a = false) (hb : b = false) :
    c = true := by
  rw [ha, Bool.false_or, hb, Bool.false_or] at h
  exact h

/-- **A BOOLEAN EQUALITY READ BACK FROM `decide`.** -/
theorem bool_eq_of_decide_true {a b : Bool} (h : decide (a = b) = true) : a = b :=
  of_decide_eq_true h

/-- **MONOCHROMATICITY, READ FORWARD.**  `monoS S t m = true` means: any two points of `S t` carry the
same colour of `col4 m`.

This is the reading `JSP90.triCase` needs in the badness transfer (`JSP90.monoS_of_all` is the other
direction). -/
theorem monoS_get {S : Fin 3 → Fin 4 → Bool} {t : Fin 3} {m : Fin 16}
    (h : monoS S t m = true) {x y : Fin 4} (hx : S t x = true) (hy : S t y = true) :
    col4 m x = col4 m y := by
  have houter := Bool.and_eq_true_iff.mp h
  have h23 : (! S t 2 || ! S t 3 || decide (col4 m 2 = col4 m 3)) = true := houter.2
  have hmid := Bool.and_eq_true_iff.mp houter.1
  have h13 : (! S t 1 || ! S t 3 || decide (col4 m 1 = col4 m 3)) = true := hmid.2
  have hlow := Bool.and_eq_true_iff.mp hmid.1
  have h12 : (! S t 1 || ! S t 2 || decide (col4 m 1 = col4 m 2)) = true := hlow.2
  have hmid0 := Bool.and_eq_true_iff.mp hlow.1
  have h03 : (! S t 0 || ! S t 3 || decide (col4 m 0 = col4 m 3)) = true := hmid0.2
  have hlo := Bool.and_eq_true_iff.mp hmid0.1
  have h01 : (! S t 0 || ! S t 1 || decide (col4 m 0 = col4 m 1)) = true := hlo.1
  have h02 : (! S t 0 || ! S t 2 || decide (col4 m 0 = col4 m 2)) = true := hlo.2
  have hxy : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  have hyy : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by omega
  rcases hxy with rfl | rfl | rfl | rfl <;> rcases hyy with rfl | rfl | rfl | rfl
  · rfl
  · exact bool_eq_of_decide_true (bool_or3_false h01 (by simp [hx]) (by simp [hy]))
  · exact bool_eq_of_decide_true (bool_or3_false h02 (by simp [hx]) (by simp [hy]))
  · exact bool_eq_of_decide_true (bool_or3_false h03 (by simp [hx]) (by simp [hy]))
  · exact (bool_eq_of_decide_true (bool_or3_false h01 (by simp [hy]) (by simp [hx]))).symm
  · rfl
  · exact bool_eq_of_decide_true (bool_or3_false h12 (by simp [hx]) (by simp [hy]))
  · exact bool_eq_of_decide_true (bool_or3_false h13 (by simp [hx]) (by simp [hy]))
  · exact (bool_eq_of_decide_true (bool_or3_false h02 (by simp [hy]) (by simp [hx]))).symm
  · exact (bool_eq_of_decide_true (bool_or3_false h12 (by simp [hy]) (by simp [hx]))).symm
  · rfl
  · exact bool_eq_of_decide_true (bool_or3_false h23 (by simp [hx]) (by simp [hy]))
  · exact (bool_eq_of_decide_true (bool_or3_false h03 (by simp [hy]) (by simp [hx]))).symm
  · exact (bool_eq_of_decide_true (bool_or3_false h13 (by simp [hy]) (by simp [hx]))).symm
  · exact (bool_eq_of_decide_true (bool_or3_false h23 (by simp [hy]) (by simp [hx]))).symm
  · rfl

/-- **THREE PAIRWISE NON-ADJACENT PAIRS MAKE AN INDEPENDENT TRIPLE.**  This is the direction the
transfer from Erdős's hypothesis needs: three points whose images are independent and distinct give
`indep3 A S a b c = true`. -/
theorem indep3_of_nadj {A : Fin 4 → Bool} {S : Fin 3 → Fin 4 → Bool} {a b c : Fin 7}
    (h1 : adj7 A S a b = false) (h2 : adj7 A S b c = false) (h3 : adj7 A S a c = false) :
    indep3 A S a b c = true := by
  unfold indep3
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (Bool.or_eq_true _ _).mpr (Or.inr (by rw [h1]; rfl))
  · exact (Bool.or_eq_true _ _).mpr (Or.inr (by rw [h2]; rfl))
  · exact (Bool.or_eq_true _ _).mpr (Or.inr (by rw [h3]; rfl))

/-- **A `Finset` WITH AT LEAST THREE POINTS HAS THREE DISTINCT POINTS.** -/
theorem three_distinct_of_card_ge_three {W : Type*} [Fintype W] (s : Finset W) (h : 3 ≤ s.card) :
    ∃ x y z : W, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp (by omega : s.card ≠ 0)
  have ht : 2 ≤ (s.erase x).card := by
    have h1 := Finset.card_erase_of_mem hx
    omega
  obtain ⟨y, hy⟩ := Finset.card_ne_zero.mp (by omega : (s.erase x).card ≠ 0)
  have hu : 1 ≤ ((s.erase x).erase y).card := by
    have h1 := Finset.card_erase_of_mem hy
    omega
  obtain ⟨z, hz⟩ := Finset.card_ne_zero.mp (by omega : ((s.erase x).erase y).card ≠ 0)
  exact ⟨x, y, z, hx, (Finset.mem_erase.mp hy).2, (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2,
    (Finset.mem_erase.mp hy).1.symm, (Finset.mem_erase.mp hz).1.symm,
    (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1.symm⟩

/-! ## Part 1 — **MISSING LEMMA 1: THE TRIANGLE CASE** -/

/-- **THE TRIANGLE CASE OF THE SEVEN-VERTEX AXIS.**  At `LocIndep 1` and `|V| ≤ 7`, a triangle `T`
whose residue `G[V \ T]` is bipartite has a vertex `t ∈ T` such that `G[(V \ T) + {t}]` is
bipartite.

This is `MISSING LEMMA 1` of `policy.json`, the one statement that `JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase`
(round 162) was waiting for.  The proof is the transfer of the graph into the `Fin 7` language of
`lean/JSPProblem/TriCount.lean`, whose counting step `JSP90.loc7_lemma` is proved there by `decide`.

Suppose no vertex of `T` is good.  `JSP90.card_cls_ge_two` forces `|V \ T| = 4` with two points in each
colour class of a proper two-colouring `d` of the residue, and `JSP90.exists_adjIn_color` forces each
of the three neighbour sets `S t` to meet both classes; the four cells `A` and the three sets `S` are
then read off the graph (`JSP90.hcrossAll`, `JSP90.hadj7`), and `JSP90.hbad8` transfers "`G[X + {t}]`
is not bipartite" into the language.  Erdős's hypothesis on the six-element set `univ \ {inv z}`
gives an independent triple avoiding each vertex `z` of the seven — `JSP90.hE` — contradicting
`JSP90.loc7_lemma`. -/
theorem triCase (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7)
    {T : Finset V} (hT : G.IsNClique 3 T) (hXbip : (deleteFinset G T).IsBipartite) :
    ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite := by
  obtain ⟨hcl, hTc3⟩ := G.isNClique_iff.mp hT
  obtain ⟨a, b, c, hab, hac, hbc, hTabc⟩ := Finset.card_eq_three.mp hTc3
  obtain ⟨d, hd⟩ := hXbip
  have hd' : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → d v ≠ d w := by
    intro v w hv hw hvw
    have h1 : (deleteFinset G T).Adj v w := by
      rw [deleteFinset_adj]
      exact ⟨hv, hw, hvw⟩
    exact hd h1
  by_cases hex : ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
  · obtain ⟨t, ht, hb⟩ := hex
    exact ⟨t, ht, hb⟩
  have hbad : ∀ t ∈ T, ¬ (deleteFinset G (T \ {t})).IsBipartite :=
    fun t ht h => hex ⟨t, ht, h⟩
  have hc0 : 2 ≤ (cls T d 0).card := card_cls_ge_two hG hT hd'
    (fun t ht => exists_adjIn_color ht hd' (hbad t ht)) hbad
  have hc1 : 2 ≤ (cls T d 1).card := card_cls_ge_two hG hT hd'
    (fun t ht => exists_adjIn_color ht hd' (hbad t ht)) hbad
  have hsub : cls T d 0 ∪ cls T d 1 ⊆ Residue T :=
    Finset.union_subset (fun x hx => mem_residue_of_notMem_set (mem_cls.mp hx).1)
      (fun x hx => mem_residue_of_notMem_set (mem_cls.mp hx).1)
  have hdisj : Disjoint (cls T d 0) (cls T d 1) := by
    refine Finset.disjoint_left.mpr (fun x h0 h1 => ?_)
    obtain ⟨-, hdx⟩ := mem_cls.mp h0
    obtain ⟨-, hdx'⟩ := mem_cls.mp h1
    exact absurd (hdx'.symm.trans hdx) (by simp)
  have hcardX : (Residue T).card = 4 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_of_disjoint hdisj
    have h3 := card_residue_le_four_of_isNClique_three hT hV
    have h4 := Finset.card_sdiff_of_subset (Finset.subset_univ T)
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  have hunion : cls T d 0 ∪ cls T d 1 = Residue T := Finset.eq_of_subset_of_card_le hsub (by
    have h2 := Finset.card_union_of_disjoint hdisj
    have h1 := Finset.card_le_card hsub
    omega)
  have hc0' : (cls T d 0).card = 2 := by
    have h2 := Finset.card_union_of_disjoint hdisj
    rw [hunion, hcardX] at h2
    omega
  have hc1' : (cls T d 1).card = 2 := by
    have h2 := Finset.card_union_of_disjoint hdisj
    rw [hunion, hcardX] at h2
    omega
  obtain ⟨p0, p1, hp01, hP⟩ := Finset.card_eq_two.mp hc0'
  obtain ⟨q0, q1, hq01, hQ⟩ := Finset.card_eq_two.mp hc1'
  have hxy : ∀ {x y : V}, x ∈ cls T d 0 → y ∈ cls T d 1 → x ≠ y := by
    intro x y hx hy he
    obtain ⟨-, hdx⟩ := mem_cls.mp hx
    obtain ⟨-, hdx'⟩ := mem_cls.mp hy
    have hde : d x = d y := by rw [he]
    have h10 : (1 : Fin 2) = 0 := by
      calc 1 = d y := hdx'.symm
        _ = d x := hde.symm
        _ = 0 := hdx
    exact absurd h10 (by simp)
  -- the two points of the first colour class, carried by `0` and `1`
  let xpt : Fin 4 → V := fun i =>
    if h : i.val = 0 then p0 else if h' : i.val = 1 then p1
      else if h'' : i.val = 2 then q0 else q1
  have hxpt0 : xpt 0 = p0 := by simp [xpt]
  have hxpt1 : xpt 1 = p1 := by simp [xpt]
  have hxpt2 : xpt 2 = q0 := by simp [xpt]
  have hxpt3 : xpt 3 = q1 := by simp [xpt]
  have hp0mem : p0 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp (by rw [hP]; simp)).1
  have hp1mem : p1 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp (by rw [hP]; simp)).1
  have hq0mem : q0 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp (by rw [hQ]; simp)).1
  have hq1mem : q1 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp (by rw [hQ]; simp)).1
  have hxpt_mem : ∀ i, xpt i ∈ Residue T := by
    intro i
    fin_cases i
    · exact hp0mem
    · exact hp1mem
    · exact hq0mem
    · exact hq1mem
  have hP0 : p0 ∈ cls T d 0 := by rw [hP]; simp
  have hP1 : p1 ∈ cls T d 0 := by rw [hP]; simp
  have hQ0 : q0 ∈ cls T d 1 := by rw [hQ]; simp
  have hQ1 : q1 ∈ cls T d 1 := by rw [hQ]; simp
  have hxpt_inj : Function.Injective xpt := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals
      first
      | exact rfl
      | exact absurd hij hp01
      | exact absurd hij hp01.symm
      | exact absurd hij hq01
      | exact absurd hij hq01.symm
      | exact absurd hij (hxy hP0 hQ0)
      | exact absurd hij (hxy hP0 hQ1)
      | exact absurd hij (hxy hP1 hQ0)
      | exact absurd hij (hxy hP1 hQ1)
      | exact absurd hij (hxy hP0 hQ0).symm
      | exact absurd hij (hxy hP0 hQ1).symm
      | exact absurd hij (hxy hP1 hQ0).symm
      | exact absurd hij (hxy hP1 hQ1).symm
  -- the three vertices of `T`, carried by `4`, `5`, `6`
  let tpt : Fin 3 → V := fun t => if h : t.val = 0 then a else if h' : t.val = 1 then b else c
  have htpt0 : tpt 0 = a := by simp [tpt]
  have htpt1 : tpt 1 = b := by simp [tpt]
  have htpt2 : tpt 2 = c := by simp [tpt]
  have haT : a ∈ T := by rw [hTabc]; simp
  have hbT : b ∈ T := by rw [hTabc]; simp
  have hcT : c ∈ T := by rw [hTabc]; simp
  have htpt_mem : ∀ t, tpt t ∈ T := by
    intro t
    fin_cases t
    · exact haT
    · exact hbT
    · exact hcT
  have htpt_inj : Function.Injective tpt := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals
      first
      | exact rfl
      | exact absurd hij hab
      | exact absurd hij hab.symm
      | exact absurd hij hac
      | exact absurd hij hac.symm
      | exact absurd hij hbc
      | exact absurd hij hbc.symm
  -- the seven vertices, carried by `Fin 7`
  let inv : Fin 7 → V := fun i =>
    if h : i.val < 4 then xpt ⟨i.val, h⟩ else tpt ⟨i.val - 4, by omega⟩
  have hxpt_surj : ∀ x ∈ Residue T, ∃ i : Fin 4, xpt i = x := by
    intro x hx
    rw [← hunion] at hx
    rcases Finset.mem_union.mp hx with hx0 | hx1
    · rw [hP] at hx0
      rcases Finset.mem_insert.mp hx0 with h | h
      · exact ⟨0, hxpt0.trans h.symm⟩
      · exact ⟨1, hxpt1.trans (Finset.mem_singleton.mp h).symm⟩
    · rw [hQ] at hx1
      rcases Finset.mem_insert.mp hx1 with h | h
      · exact ⟨2, hxpt2.trans h.symm⟩
      · exact ⟨3, hxpt3.trans (Finset.mem_singleton.mp h).symm⟩
  have invX : ∀ (k : Fin 7) (hk : (k : ℕ) < 4), inv k = xpt ⟨k.val, hk⟩ := by
    intro k hk
    obtain ⟨kv, kvlt⟩ := k
    have hk' : kv < 4 := by simpa using hk
    have hkv : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 := by omega
    rcases hkv with rfl | rfl | rfl | rfl <;> simp [inv]
  have invT : ∀ (k : Fin 7) (hk : ¬ (k : ℕ) < 4),
      inv k = tpt ⟨k.val - 4, by omega⟩ := by
    intro k hk
    obtain ⟨kv, kvlt⟩ := k
    have hk' : ¬ kv < 4 := by simpa using hk
    have hkv : kv = 4 ∨ kv = 5 ∨ kv = 6 := by omega
    rcases hkv with rfl | rfl | rfl <;> simp [inv]
  have hxpt_notMem : ∀ i : Fin 4, xpt i ∉ T := fun i => mem_residue.mp (hxpt_mem i)
  have hResSub : Residue T ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have inv_mem : ∀ i, inv i ∈ (Finset.univ : Finset V) := by
    intro i
    by_cases h : i.val < 4
    · rw [invX i h]
      exact hResSub (hxpt_mem ⟨i.val, h⟩)
    · rw [invT i h]
      exact Finset.mem_univ _
  have inv_inj : Function.Injective inv := by
    intro i j hij
    by_cases hi4 : (i : ℕ) < 4
    · by_cases hj4 : (j : ℕ) < 4
      · have hEq : xpt ⟨i.val, hi4⟩ = xpt ⟨j.val, hj4⟩ := by
          rw [← invX i hi4, hij, invX j hj4]
        have hEq4 : (⟨i.val, hi4⟩ : Fin 4) = ⟨j.val, hj4⟩ := hxpt_inj hEq
        refine Fin.val_injective ?_
        simpa using congrArg Fin.val hEq4
      · have hEq : xpt ⟨i.val, hi4⟩ = tpt ⟨j.val - 4, by omega⟩ := by
          rw [← invX i hi4, hij, invT j hj4]
        exact absurd (hEq ▸ htpt_mem ⟨j.val - 4, by omega⟩) (hxpt_notMem ⟨i.val, hi4⟩)
    · by_cases hj4 : j.val < 4
      · have hEq : tpt ⟨i.val - 4, by omega⟩ = xpt ⟨j.val, hj4⟩ := by
          rw [← invT i hi4, hij, invX j hj4]
        exact absurd (hEq ▸ htpt_mem ⟨i.val - 4, by omega⟩) (hxpt_notMem ⟨j.val, hj4⟩)
      · have hEq : tpt ⟨i.val - 4, by omega⟩ = tpt ⟨j.val - 4, by omega⟩ := by
          rw [← invT i hi4, hij, invT j hj4]
        have hEq3 : (⟨i.val - 4, by omega⟩ : Fin 3) = ⟨j.val - 4, by omega⟩ := htpt_inj hEq
        refine Fin.val_injective ?_
        have h2 : (i : ℕ) - 4 = (j : ℕ) - 4 := congrArg Fin.val hEq3
        omega
  have hinv4 : inv 4 = a := by
    rw [invT 4 (by decide)]
    exact htpt0
  have hinv5 : inv 5 = b := by
    rw [invT 5 (by decide)]
    exact htpt1
  have hinv6 : inv 6 = c := by
    rw [invT 6 (by decide)]
    exact htpt2
  have inv_surj : ∀ x : V, ∃ i : Fin 7, inv i = x := by
    intro x
    by_cases hxT : x ∈ T
    · rw [hTabc] at hxT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with rfl | rfl | rfl
      · exact ⟨4, hinv4⟩
      · exact ⟨5, hinv5⟩
      · exact ⟨6, hinv6⟩
    · obtain ⟨i, hi⟩ := hxpt_surj x (mem_residue_of_notMem_set hxT)
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      rw [invX ⟨i.val, by omega⟩ (show i.val < 4 from i.isLt), hi]
  have hVcard : Fintype.card V = 7 := by
    have h1 := Finset.card_sdiff_of_subset (Finset.subset_univ T)
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    have h2 : ((Finset.univ : Finset V) \ T).card = 4 := by
      rw [Residue] at hcardX
      exact hcardX
    have h3 : T.card = 3 := hTc3
    omega
  -- the four cells of `G[X]`
  let A : Fin 4 → Bool := fun i =>
    if h : i.val = 0 then decide (G.Adj p0 q0)
      else if h' : i.val = 1 then decide (G.Adj p0 q1)
        else if h'' : i.val = 2 then decide (G.Adj p1 q0)
          else if hC : i.val = 3 then decide (G.Adj p1 q1) else false
  -- the neighbours of `t` inside `X`
  let S : Fin 3 → Fin 4 → Bool := fun t i => decide (G.Adj (tpt t) (xpt i))
  have hp0d : d p0 = 0 := (mem_cls.mp (by rw [hP]; simp)).2
  have hp1d : d p1 = 0 := (mem_cls.mp (by rw [hP]; simp)).2
  have hq0d : d q0 = 1 := (mem_cls.mp (by rw [hQ]; simp)).2
  have hq1d : d q1 = 1 := (mem_cls.mp (by rw [hQ]; simp)).2
  have hidx : ∀ i : Fin 4, (d (xpt i) = 0 ∧ i.val < 2) ∨ (d (xpt i) = 1 ∧ 2 ≤ i.val) := by
    intro i
    fin_cases i
    · exact Or.inl ⟨by simp [xpt, hxpt0, hp0d], by decide⟩
    · exact Or.inl ⟨by simp [xpt, hxpt1, hp1d], by decide⟩
    · exact Or.inr ⟨by simp [xpt, hxpt2, hq0d], by decide⟩
    · exact Or.inr ⟨by simp [xpt, hxpt3, hq1d], by decide⟩
  have hproperX : ∀ v w : V, v ∉ T → w ∉ T → G.Adj v w → d v = d w → False :=
    fun v w hv hw hh hde => hd' hv hw hh hde
  have hnp01 : ¬ G.Adj p0 p1 := by
    intro hh
    have hadj : G.Adj (xpt 0) (xpt 1) := by rw [hxpt0, hxpt1]; exact hh
    have hde : d p0 = d p1 := hp0d.trans hp1d.symm
    exact hproperX p0 p1 (hxpt_notMem 0) (hxpt_notMem 1) hadj hde
  have hnp10 : ¬ G.Adj p1 p0 := by
    intro hh
    have hadj : G.Adj (xpt 1) (xpt 0) := by rw [hxpt1, hxpt0]; exact hh
    have hde : d p1 = d p0 := hp1d.trans hp0d.symm
    exact hproperX p1 p0 (hxpt_notMem 1) (hxpt_notMem 0) hadj hde
  have hnq01 : ¬ G.Adj q0 q1 := by
    intro hh
    have hadj : G.Adj (xpt 2) (xpt 3) := by rw [hxpt2, hxpt3]; exact hh
    have hde : d q0 = d q1 := hq0d.trans hq1d.symm
    exact hproperX q0 q1 (hxpt_notMem 2) (hxpt_notMem 3) hadj hde
  have hnq10 : ¬ G.Adj q1 q0 := by
    intro hh
    have hadj : G.Adj (xpt 3) (xpt 2) := by rw [hxpt3, hxpt2]; exact hh
    have hde : d q1 = d q0 := hq1d.trans hq0d.symm
    exact hproperX q1 q0 (hxpt_notMem 3) (hxpt_notMem 2) hadj hde
  have hcrossAll : ∀ p q : Fin 4, cross A p q = decide (G.Adj (xpt p) (xpt q)) := by
    intro p q
    obtain ⟨pv, pvlt⟩ := p
    obtain ⟨qv, qvlt⟩ := q
    have hpv : pv = 0 ∨ pv = 1 ∨ pv = 2 ∨ pv = 3 := by omega
    have hqv : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 := by omega
    rcases hpv with rfl | rfl | rfl | rfl <;> rcases hqv with rfl | rfl | rfl | rfl <;>
      simp [cross, A, xpt, adj_comm, hnp01, hnp10, hnq01, hnq10]
  have habAdj : G.Adj a b := hcl haT hbT hab
  have hacAdj : G.Adj a c := hcl haT hcT hac
  have hbcAdj : G.Adj b c := hcl hbT hcT hbc
  have hadj7 : ∀ (i j : Fin 7), adj7 A S i j = decide (G.Adj (inv i) (inv j)) := by
    intro i j
    obtain ⟨iv, ivlt⟩ := i
    obtain ⟨jv, jvlt⟩ := j
    have hi7 : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 ∨ iv = 5 ∨ iv = 6 := by omega
    have hj7 : jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3 ∨ jv = 4 ∨ jv = 5 ∨ jv = 6 := by omega
    rcases hi7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [adj7, xIdx, tIdx, inv, cross, A, S, xpt, tpt, hnp01, hnp10, hnq01, hnq10,
        hxpt0, hxpt1, hxpt2, hxpt3, htpt0, htpt1, htpt2, adj_comm,
        habAdj, hacAdj, hbcAdj]
  -- **THE THREE NEIGHBOUR SETS HAVE EMPTY TRIPLE INTERSECTION.**
  have htri : ∀ i : Fin 4, S 0 i = true → S 1 i = true → S 2 i = true → False := by
    intro i h0 h1 h2
    have hS0 : S 0 i = decide (G.Adj a (xpt i)) := by simp [S, htpt0]
    have hS1 : S 1 i = decide (G.Adj b (xpt i)) := by simp [S, htpt1]
    have hS2 : S 2 i = decide (G.Adj c (xpt i)) := by simp [S, htpt2]
    have hAdj0 : G.Adj a (xpt i) := of_decide_eq_true (hS0 ▸ h0)
    have hAdj1 : G.Adj b (xpt i) := of_decide_eq_true (hS1 ▸ h1)
    have hAdj2 : G.Adj c (xpt i) := of_decide_eq_true (hS2 ▸ h2)
    have hsub : T ⊆ AdjIn G (xpt i) T := by
      intro w hw
      rw [hTabc] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw
      · subst hw
        exact mem_adjIn.mpr ⟨by rw [hTabc]; simp, hAdj0.symm⟩
      · subst hw
        exact mem_adjIn.mpr ⟨by rw [hTabc]; simp, hAdj1.symm⟩
      · subst hw
        exact mem_adjIn.mpr ⟨by rw [hTabc]; simp, hAdj2.symm⟩
    have hle := card_adjIn_le_two_of_isNClique_three hG hT (x := xpt i) (hxpt_notMem i)
    have hcard := Finset.card_le_card hsub
    have h3 : T.card = 3 := hTc3
    omega
  -- **EACH NEIGHBOUR SET MEETS BOTH COLOUR CLASSES.**
  have hbi0 : ∀ t : Fin 3, S t 0 = true ∨ S t 1 = true := by
    intro t
    obtain ⟨x, hx1, hxT, hx0⟩ := exists_adjIn_color (htpt_mem t) hd' (hbad (tpt t) (htpt_mem t)) (i := 0)
    have hxf : x ∈ cls T d 0 := mem_cls.mpr ⟨hxT, hx0⟩
    have hxf' : x = p0 ∨ x = p1 := by
      have hx2 : x ∈ insert p0 (singleton p1 : Finset V) := by
        show x ∈ ({p0, p1} : Finset V)
        rw [← hP]; exact hxf
      rcases Finset.mem_insert.mp hx2 with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hxf' with h | h
    · refine Or.inl ?_
      have hAdj : G.Adj (tpt t) (xpt 0) := by rw [hxpt0, ← h]; exact hx1
      have hEq : S t 0 = decide (G.Adj (tpt t) (xpt 0)) := by simp [S, htpt0]
      exact hEq ▸ decide_eq_true hAdj
    · refine Or.inr ?_
      have hAdj : G.Adj (tpt t) (xpt 1) := by rw [hxpt1, ← h]; exact hx1
      have hEq : S t 1 = decide (G.Adj (tpt t) (xpt 1)) := by simp [S, htpt1]
      exact hEq ▸ decide_eq_true hAdj
  have hbi1 : ∀ t : Fin 3, S t 2 = true ∨ S t 3 = true := by
    intro t
    obtain ⟨x, hx1, hxT, hx1'⟩ := exists_adjIn_color (htpt_mem t) hd' (hbad (tpt t) (htpt_mem t)) (i := 1)
    have hxf : x ∈ cls T d 1 := mem_cls.mpr ⟨hxT, hx1'⟩
    have hxf' : x = q0 ∨ x = q1 := by
      have hx2 : x ∈ insert q0 (singleton q1 : Finset V) := by
        show x ∈ ({q0, q1} : Finset V)
        rw [← hQ]; exact hxf
      rcases Finset.mem_insert.mp hx2 with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hxf' with h | h
    · refine Or.inl ?_
      have hAdj : G.Adj (tpt t) (xpt 2) := by rw [hxpt2, ← h]; exact hx1
      have hEq : S t 2 = decide (G.Adj (tpt t) (xpt 2)) := by simp [S, htpt0]
      exact hEq ▸ decide_eq_true hAdj
    · refine Or.inr ?_
      have hAdj : G.Adj (tpt t) (xpt 3) := by rw [hxpt3, ← h]; exact hx1
      have hEq : S t 3 = decide (G.Adj (tpt t) (xpt 3)) := by simp [S, htpt0]
      exact hEq ▸ decide_eq_true hAdj
  -- the seven vertices, indexed from the residue side
  let finv : V → Fin 7 := fun v => Classical.choose (inv_surj v)
  have finv_spec : ∀ v, inv (finv v) = v := fun v => Classical.choose_spec (inv_surj v)
  have hfinv4 : ∀ v : V, v ∉ T → (finv v).val < 4 := by
    intro v hvT
    by_contra hc
    have hge : 4 ≤ (finv v).val := by omega
    have hvv : inv (finv v) = tpt ⟨(finv v).val - 4, by omega⟩ := invT _ (by omega)
    have hmem : v ∈ T := by
      rw [← finv_spec v, hvv]
      exact htpt_mem ⟨(finv v).val - 4, by omega⟩
    exact hvT hmem
  have finv_adj : ∀ v w : V, G.Adj v w → G.Adj (inv (finv v)) (inv (finv w)) := by
    intro v w h
    rw [finv_spec v, finv_spec w]
    exact h
  -- **EACH VERTEX OF `T` IS BAD IN THE `Fin 7` LANGUAGE.**
  have hbad8 : ∀ t : Fin 3, bad8 A S t := by
    intro t m hm
    obtain ⟨hmono, hprop⟩ := hm
    have hmono : ∀ (x y : Fin 4), S t x = true → S t y = true → col4 m x = col4 m y :=
      fun x y hx hy => monoS_get hmono hx hy
    -- the two-colouring of the residue read off the colouring index `m`
    let e : V → Fin 2 :=
      fun v => if hv : (finv v).val < 4 then bitCol (col4 m ⟨(finv v).val, hv⟩) else 0
    have hproper : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → e v ≠ e w := by
      intro v w hvT hwT hAdj
      have h4v := hfinv4 v hvT
      have h4w := hfinv4 w hwT
      have hvi : inv (finv v) = xpt ⟨(finv v).val, h4v⟩ := invX _ h4v
      have hwi : inv (finv w) = xpt ⟨(finv w).val, h4w⟩ := invX _ h4w
      have hc : cross A ⟨(finv v).val, h4v⟩ ⟨(finv w).val, h4w⟩ = true := by
        rw [hcrossAll ⟨(finv v).val, h4v⟩ ⟨(finv w).val, h4w⟩, ← hvi, ← hwi]
        exact decide_eq_true (finv_adj v w hAdj)
      simp only [e, dif_pos h4v, dif_pos h4w]
      exact fun heq => proper8_adj A m ⟨(finv v).val, h4v⟩ ⟨(finv w).val, h4w⟩ hprop hc
        (bitCol_inj _ _ heq)
    have hSj : ∀ (x : V) (j : Fin 4) (hj : xpt j = x),
        S t j = decide (G.Adj (tpt t) x) := by
      intro x j hj
      simp only [S]
      rw [hj]
    by_cases hex : ∃ x : Fin 4, S t x = true
    · obtain ⟨x0, hx0⟩ := hex
      have hx0' : S t ⟨x0.val, x0.isLt⟩ = true := by simpa using hx0
      refine hbad (tpt t) (htpt_mem t)
        (isBipartite_of_adjIn_mono (T := T) (t := tpt t) (ht := htpt_mem t) hproper
          (i := bitCol (col4 m ⟨x0.val, x0.isLt⟩)) ?_)
      intro x hx hxT
      have h4 : (finv x).val < 4 := hfinv4 x hxT
      have hj : xpt ⟨(finv x).val, h4⟩ = x := by
        rw [← invX _ h4]
        exact finv_spec x
      have hsx : S t ⟨(finv x).val, h4⟩ = true :=
        (hSj x ⟨(finv x).val, h4⟩ hj) ▸ decide_eq_true hx
      simp only [e, dif_pos h4]
      rw [hmono _ _ hsx hx0']
    · have hno : ∀ j : Fin 4, S t j ≠ true := fun j hj => hex ⟨j, hj⟩
      refine hbad (tpt t) (htpt_mem t)
        (isBipartite_of_adjIn_mono (T := T) (t := tpt t) (ht := htpt_mem t) hproper (i := 0) ?_)
      intro x hx hxT
      have h4 : (finv x).val < 4 := hfinv4 x hxT
      have hj : xpt ⟨(finv x).val, h4⟩ = x := by
        rw [← invX _ h4]
        exact finv_spec x
      exact False.elim (hno ⟨(finv x).val, h4⟩
        ((hSj x ⟨(finv x).val, h4⟩ hj) ▸ decide_eq_true hx))
  -- **ERDŐS'S HYPOTHESIS, READ ON THE SIX-ELEMENT SETS.**
  have hE : ∀ z : Fin 7, hasTripleAvoiding A S z = true := by
    intro z
    obtain ⟨S₀, hS₀sub, hS₀ind, hS₀card⟩ := hG ((Finset.univ : Finset V) \ {inv z})
    have hcard6 : ((Finset.univ : Finset V) \ {inv z}).card = 6 := by
      have h1 := Finset.card_erase_of_mem (Finset.mem_univ (inv z))
      have h2 : ((Finset.univ : Finset V) \ {inv z}) = Finset.univ.erase (inv z) := by
        ext x
        simp
      rw [h2, h1]
      have h3 : (Finset.univ : Finset V).card = 7 := by
        rw [Finset.card_univ]
        exact hVcard
      omega
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, h12, h23, h13⟩ :=
      three_distinct_of_card_ge_three S₀ (by omega)
    have hz1 : x1 ≠ inv z := fun h => (Finset.mem_sdiff.mp (hS₀sub hx1)).2 (Finset.mem_singleton.mpr h)
    have hz2 : x2 ≠ inv z := fun h => (Finset.mem_sdiff.mp (hS₀sub hx2)).2 (Finset.mem_singleton.mpr h)
    have hz3 : x3 ≠ inv z := fun h => (Finset.mem_sdiff.mp (hS₀sub hx3)).2 (Finset.mem_singleton.mpr h)
    have hnotAdj : ∀ {v w : V}, v ∈ S₀ → w ∈ S₀ → v ≠ w → G.Adj v w → False := by
      intro v w hv hw hne hh
      exact hS₀ind (show v ∈ (↑S₀ : Set V) from hv) (show w ∈ (↑S₀ : Set V) from hw) hne hh
    obtain ⟨a1, ha1⟩ := inv_surj x1
    obtain ⟨a2, ha2⟩ := inv_surj x2
    obtain ⟨a3, ha3⟩ := inv_surj x3
    have hab : a1 ≠ a2 := by
      intro he
      exact h12 (calc x1 = inv a1 := ha1.symm
        _ = inv a2 := by rw [he]
        _ = x2 := ha2)
    have hac : a1 ≠ a3 := by
      intro he
      exact h13 (calc x1 = inv a1 := ha1.symm
        _ = inv a3 := by rw [he]
        _ = x3 := ha3)
    have hbc : a2 ≠ a3 := by
      intro he
      exact h23 (calc x2 = inv a2 := ha2.symm
        _ = inv a3 := by rw [he]
        _ = x3 := ha3)
    have hn1 : adj7 A S a1 a2 = false := by
      rw [hadj7]
      exact decide_eq_false (fun hh => hnotAdj hx1 hx2 h12 (ha2 ▸ (ha1 ▸ hh)))
    have hn2 : adj7 A S a2 a3 = false := by
      rw [hadj7]
      exact decide_eq_false (fun hh => hnotAdj hx2 hx3 h23 (ha3 ▸ (ha2 ▸ hh)))
    have hn3 : adj7 A S a1 a3 = false := by
      rw [hadj7]
      exact decide_eq_false (fun hh => hnotAdj hx1 hx3 h13 (ha3 ▸ (ha1 ▸ hh)))
    have hindo : indep3 A S a1 a2 a3 = true := indep3_of_nadj hn1 hn2 hn3
    have haz1 : a1 ≠ z := by
      intro he
      exact hz1 (calc x1 = inv a1 := ha1.symm
        _ = inv z := by rw [he]
        _ = inv z := rfl)
    have haz2 : a2 ≠ z := by
      intro he
      exact hz2 (calc x2 = inv a2 := ha2.symm
        _ = inv z := by rw [he]
        _ = inv z := rfl)
    have haz3 : a3 ≠ z := by
      intro he
      exact hz3 (calc x3 = inv a3 := ha3.symm
        _ = inv z := by rw [he]
        _ = inv z := rfl)
    exact hasTripleAvoiding_of_indep3 hab hbc hac hindo haz1 haz2 haz3
  exact absurd hE (loc7_lemma A S (hyps_of hbi0 hbi1 htri hbad8))

/-! ## Part 2 — two small counting lemmas

`JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase` (round 162) asks for the triangle case of
*every* triangle, while `JSP90.triCase` is stated with a bipartite residue.  The bridge is already in
the development: `JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven`
(`lean/JSPProblem/Seven.lean`, round 150) proves the residue of every triangle bipartite, from
`JSP90.not_isNClique_three_of_disjoint_of_locIndep_one` — at `LocIndep 1` there are no two
vertex-disjoint triangles, because an independent set meets each of the two triangles in at most one
point while Erdős's hypothesis on the six points `T ∪ D` demands three.  This file re-proves that
bridge from scratch and adds the two counting lemmas it consumes:

* **`JSP90.exists_two_ne_of_card_ge_two`** — two distinct points of a `Finset` of size `≥ 2`;
* **`JSP90.card_inter_le_one_of_isNClique_three_indep`** — **an independent set meets a triangle in at
  most one point**, the `|S ∩ T| ≤ 1` of that argument in reusable form.

-/

/-- **TWO DISTINCT POINTS OF A `Finset` WITH AT LEAST TWO ELEMENTS.** -/
theorem exists_two_ne_of_card_ge_two {W : Type*} [Fintype W] (s : Finset W) (h : 2 ≤ s.card) :
    ∃ x y : W, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp (by omega : s.card ≠ 0)
  have h1 : 1 ≤ (s.erase x).card := by
    have h2 := Finset.card_erase_of_mem hx
    omega
  obtain ⟨y, hy⟩ := Finset.card_ne_zero.mp (by omega : (s.erase x).card ≠ 0)
  exact ⟨x, y, hx, (Finset.mem_erase.mp hy).2, (Finset.mem_erase.mp hy).1.symm⟩

/-- **AN INDEPENDENT SET MEETS A TRIANGLE IN AT MOST ONE POINT.** -/
theorem card_inter_le_one_of_isNClique_three_indep {C s : Finset V} (hC : G.IsNClique 3 C)
    (hs : G.IsIndepSet s) : (s ∩ C).card ≤ 1 := by
  by_contra hc
  have h2 : 2 ≤ (s ∩ C).card := by omega
  obtain ⟨x, y, hxs, hys⟩ := exists_two_ne_of_card_ge_two (s ∩ C) h2
  obtain ⟨hxsC, hxC⟩ := Finset.mem_inter.mp hxs
  obtain ⟨hysC, hyC⟩ := Finset.mem_inter.mp hys.1
  have hcl : (↑C : Set V).Pairwise G.Adj := (G.isNClique_iff.mp hC).1
  exact (hs (show x ∈ (↑s : Set V) from hxsC) (show y ∈ (↑s : Set V) from hysC) hys.2)
    (hcl (show x ∈ (↑C : Set V) from hxC) (show y ∈ (↑C : Set V) from hyC) hys.2)

/-! ## Part 3 — **ERDŐS #73 AT `k = 1` ON SEVEN VERTICES, WITH THE OPTIMAL CONSTANT `2`** -/

/-- **THE SEVEN-VERTEX AXIS WITH THE OPTIMAL CONSTANT `2`.**

```lean
LocIndep 1 G → |V| ≤ 7 → CloseToBipartite 2 G
```

The constant `2` is optimal (`lean/JSPProblem/Six.lean`: the three-sun `sun3` satisfies `LocIndep 1`
and has transversal number `2`), so this is a sharp instance of the headline theorem.  A shortest odd
cycle of `G` has three, five or seven vertices, and the two long cases were closed in rounds 162
(`JSP90.closeToBipartite_one_of_shortest_five`, `JSP90.closeToBipartite_one_of_shortest_oddCycle_of_card_eq`).
In the triangle case the residue is bipartite (Part 2) and `JSP90.triCase` (Part 1) produces the
vertex `t` whose deletion makes the residue-plus-`t` bipartite, so
`JSP90.closeToBipartite_of_residue` turns that into `CloseToBipartite (0 + |T \ {t}|) G`. -/
theorem closeToBipartite_two_of_locIndep_one_card_le_seven (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 7) : CloseToBipartite 2 G := by
  by_cases hne : Nonempty V
  · by_cases htf : ∀ D : Finset V, ¬ G.IsNClique 3 D
    · obtain ⟨X, hX, hbis⟩ := closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree
        hV htf hne
      exact ⟨X, (Nat.le_trans hX (by decide)), hbis⟩
    · obtain ⟨T, hT0⟩ := not_forall.mp htf
      have hT : G.IsNClique 3 T := Classical.byContradiction hT0
      obtain ⟨t, ht, hres⟩ := triCase hG hV hT
        (isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven hG hV hT)
      have hcard : (T \ {t}).card = 2 := by
        have h1 : ({t} : Finset V).card = 1 := Finset.card_singleton t
        have h2 := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ht)
        have h3 : T.card = 3 := (G.isNClique_iff.mp hT).2
        omega
      have hres' : CloseToBipartite 0 (deleteFinset G (T \ {t})) := by
        refine ⟨∅, by simp, ?_⟩
        simpa [deleteFinset_empty] using hres
      have h1 := closeToBipartite_of_residue (C := T \ {t}) (q := 0) hres'
      obtain ⟨X, hX, hbis⟩ := h1
      exact ⟨X, by omega, hbis⟩
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    refine isBipartite_of_no_oddCycle (fun h => ?_)
    obtain ⟨D, hD⟩ := h
    obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
      have hz := isOddCycle_card_ge_three hD
      omega)
    exact absurd ⟨z⟩ hne

/-- **The class of the instance, in the shape without the triangle-free hypothesis.** -/
def LocIndepOneAllSmallOrder.{w} (m n : ℕ) : Prop :=
  ∀ (W : Type w) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W ≤ n → LocIndep 1 G →
    CloseToBipartite m G

/-- **ERDŐS #73 AT `k = 1`, CONSTANT `2`, ON GRAPHS OF ORDER AT MOST SEVEN — A NEW INSTANCE OF THE
HEADLINE THEOREM, WITH THE OPTIMAL CONSTANT.** -/
theorem erdos73On_one_two_of_card_le_seven : LocIndepOneAllSmallOrder.{u} 2 7 :=
  fun _ _ G hV hG => closeToBipartite_two_of_locIndep_one_card_le_seven hG hV

/-- **The odd cycle transversal number is at most `2` at `LocIndep 1` and `|V| ≤ 7`.** -/
theorem tauOdd_le_two_of_locIndep_one_card_le_seven (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 7) : tauOdd G ≤ 2 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_card_le_seven hG hV)

/-- **A TWO-ELEMENT ODD CYCLE TRANSVERSAL EXISTS at `LocIndep 1` and `|V| ≤ 7`.** -/
theorem exists_hitsOddCycles_two_of_locIndep_one_card_le_seven (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 7) : ∃ X : Finset V, X.card ≤ 2 ∧ HitsOddCycles G X :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_card_le_seven hG hV)

/-- **THE SEVEN-VERTEX INSTANCE IN THE PIECE FORM**, i.e. the form a decomposition argument reads:
a `LocIndep 1` graph induced on a vertex set of at most seven vertices is two vertices away from
bipartite.  This is `JSP90.closeToBipartite_two_of_locIndep_one_of_card_le` (six vertices,
`lean/JSPProblem/Six.lean`) with the optimal seven-vertex constant. -/
theorem closeToBipartite_two_of_locIndep_one_of_card_le_seven (hG : LocIndep 1 G) {U : Finset V}
    (hU : U.card ≤ 7) : CloseToBipartite 2 (induceFinset G U) :=
  closeToBipartite_pieceOf_closeToBipartite_of_card_le (m := 2) (n := 7)
    erdos73On_one_two_of_card_le_seven hG hU

/-! ### The piece form in the transversal shape — what a peeling argument consumes -/

/-- **THE SEVEN-VERTEX PIECE, TRANSVERSAL FORM.**  Inside any vertex set `U` of at most seven
vertices there is a set of at most two vertices of `U` meeting every odd cycle of `G[U]`.

This is the form in which a decomposition (peeling pieces of order `≤ 7` one at a time) reads the
instance, and it is new: `JSP90.closeToBipartite_two_of_locIndep_one_of_card_le` gives the
`CloseToBipartite` shape at six vertices only. -/
theorem exists_hitsOddCycles_two_of_card_le_seven (hG : LocIndep 1 G) {U : Finset V}
    (hU : U.card ≤ 7) :
    ∃ X : Finset V, X ⊆ U ∧ X.card ≤ 2 ∧ HitsOddCycles (induceFinset G U) X := by
  obtain ⟨X, hX, hbis⟩ := closeToBipartite_two_of_locIndep_one_of_card_le_seven hG hU
  have hbis' : CloseToBipartite 2 (induceFinset G U) := ⟨X, hX, hbis⟩
  obtain ⟨Y, hY, hhits⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := induceFinset G U) (m := 2)).mp hbis'
  refine ⟨Y ∩ U, Finset.inter_subset_right, ?_, ?_⟩
  · exact Nat.le_trans (Finset.card_le_card Finset.inter_subset_left) hY
  · intro D hD hnot
    obtain ⟨hD', hDsub⟩ := isOddCycle_induceFinset hD
    refine hhits D hD (Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_))
    obtain ⟨hxD, hxY⟩ := Finset.mem_inter.mp hx
    exact Finset.notMem_empty x (hnot ▸ Finset.mem_inter.mpr
      ⟨hxD, Finset.mem_inter.mpr ⟨hxY, hDsub hxD⟩⟩)

/-- **THE ODD CYCLE TRANSVERSAL NUMBER OF A SEVEN-VERTEX PIECE IS AT MOST `2`.** -/
theorem tauOdd_le_two_of_card_le_seven (hG : LocIndep 1 G) {U : Finset V} (hU : U.card ≤ 7) :
    tauOdd (induceFinset G U) ≤ 2 :=
  (closeToBipartite_iff_tauOdd_le (G := induceFinset G U) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_of_card_le_seven hG hU)

/-! ### Optimality of the constant `2`

`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` cannot be improved to the constant `1`:
`JSP90.sun3` (six vertices, `lean/JSPProblem/Sun.lean`) satisfies Erdős's hypothesis with `k = 1`
(`JSP90.locIndep_one_sun3`) and is not one vertex away from bipartite
(`JSP90.not_closeToBipartite_one_sun3`). -/

/-- **THE ODD CYCLE TRANSVERSAL NUMBER OF THE THREE-SUN IS EXACTLY `2`** — the sharp witness for the
seven-vertex instance. -/
theorem tauOdd_sun3 : tauOdd sun3 = 2 := by
  have h1 : tauOdd sun3 ≤ 2 :=
    tauOdd_le_two_of_locIndep_one_card_le_seven (V := Fin 6) (G := sun3) locIndep_one_sun3 (by decide)
  have h2 : 2 ≤ tauOdd sun3 := by
    by_contra hc
    exact not_closeToBipartite_one_sun3
      ((closeToBipartite_iff_tauOdd_le (G := sun3) (m := 1)).mpr (by omega))
  omega

/-- **THE BEST UNIVERSAL CONSTANT AT `k = 1` AND `|V| ≤ 7` IS EXACTLY `2`.**  The class of graphs of
order at most seven satisfying Erdős's hypothesis with `k = 1` is two vertices away from bipartite
(`JSP90.erdos73On_one_two_of_card_le_seven`) and **not** one vertex away (this statement). -/
theorem not_locIndepOneAllSmallOrder_one_of_card_le_seven : ¬ LocIndepOneAllSmallOrder.{0} 1 7 := by
  intro h
  have h1 : CloseToBipartite 1 sun3 := by
    unfold LocIndepOneAllSmallOrder at h
    exact h (Fin 6) (inferInstance : Fintype (Fin 6)) sun3 (by decide) locIndep_one_sun3
  exact not_closeToBipartite_one_sun3 h1

end
end JSP90