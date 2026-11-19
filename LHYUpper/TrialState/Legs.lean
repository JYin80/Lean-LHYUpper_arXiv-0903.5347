import LHYUpper.TrialState.Reorder

/-!
# Matrix elements with few legs: §7, §8, §9, §10

The unique `γ ∈ M` with `𝓐^v γ = α` of (7.29) [gammaDaal], the classification of the legs of
`⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ ≠ 0` (Lemma 8.1 [posscombone0]) and of
`⟨α| a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} |β⟩ ≠ 0` (Lemma 9.1 [fourlegslemma1], with the case
`v₁, v₂ ∈ P_{H,c}`, `v₃, v₄ ∈ P_L` included), the values of `F(α) + F(β)` of (8.9) [defFal] and
(8.10) [fab=no], and the matrix-element identity (10.9) [11.1].

A nonzero coefficient of `a†_p a†_q a_r a_s` means that nothing is truncated, so that
`α + δ_s + δ_r = β + δ_q + δ_p` exactly; the arguments below use this identity together with the
symmetry of `α, β ∈ M` on `P_I ∪ (P_H ∖ P_{H,c})`, the parity of the number of particles in
`P_{H,c}`, and `α*(u) - α(u) ∈ {0, 1}` on `P_L`.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

section Legs
variable {V w : R3 → ℝ} {ρ L kc : ℝ} {N : ℕ}

/-- `F(α)` of (8.9) [defFal]. -/
def Fal (ρ L : ℝ) {n : ℕ} (v : Fin n → Idx) (α : Occ) : ℕ :=
  ∑ i, if inPL ρ L (v i) then Int.natAbs ((α (v i) : ℤ) - α (-(v i))) else 0

private lemma Legs_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

private lemma Legs_pm_symm {a b : Idx} (h : Legs_pm a b) : Legs_pm b a :=
  ⟨Ne.symm h.1, fun e => h.2 (by rw [e, neg_neg])⟩

/-- A nonzero coefficient of `a†_p a†_q a_r a_s` on `|β⟩` means that nothing is truncated:
`α + δ_s + δ_r = β + δ_q + δ_p` for the resulting state `α`. -/
private lemma Legs_a4_id {p q r s : Idx} {α β : Occ} (hne : (a4 p q r s β).1 ≠ 0)
    (heq : (a4 p q r s β).2 = α) :
    1 ≤ β s ∧ 1 ≤ β r ∧ 1 ≤ α p ∧ 1 ≤ α q ∧
      α + Finsupp.single s 1 + Finsupp.single r 1 =
        β + Finsupp.single q 1 + Finsupp.single p 1 := by
  have hpos : 1 ≤ β s ∧ 1 ≤ ((β - Finsupp.single s 1 : Occ) r) := by
    simp only [a4] at hne
    rw [mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff] at hne
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hne
    rw [Ne, Real.sqrt_eq_zero', not_le] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  obtain ⟨h1, h2⟩ := hpos
  subst heq
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply] at h2
  have key : ∀ n : Idx, ((a4 p q r s β).2 n) + (if s = n then 1 else 0) + (if r = n then 1 else 0)
      = β n + (if q = n then 1 else 0) + (if p = n then 1 else 0) := by
    intro n
    simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    by_cases hs : s = n <;> by_cases hr : r = n <;> subst_vars <;> simp_all <;> omega
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · split_ifs at h2 <;> omega
  · simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs <;> omega
  · simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs <;> omega
  · ext n
    have := key n
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    omega

/-- The exact identity, pointwise. -/
private lemma Legs_id_apply {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1) (n : Idx) :
    α n + (if s = n then 1 else 0) + (if r = n then 1 else 0) =
      β n + (if q = n then 1 else 0) + (if p = n then 1 else 0) := by
  have := DFunLike.congr_fun h n
  simpa only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] using this

/-- The total momentum of an occupation is additive. -/
private lemma Legs_mom_add (f g : Occ) :
    (f + g).sum (fun n m => m • n) = f.sum (fun n m => m • n) + g.sum (fun n m => m • n) :=
  Finsupp.sum_add_index' (fun n => zero_smul ℕ n) (fun n a b => add_smul a b n)

private lemma Legs_mom_single (n : Idx) :
    (Finsupp.single n 1 : Occ).sum (fun n m => m • n) = n := by
  simp [Finsupp.sum_single_index]

/-- Momentum conservation `p + q = r + s` from the exact identity between two elements of `M`. -/
private lemma Legs_mom (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1) : p + q = r + s := by
  have h1 := MBasic_momentum hρ hα
  have h2 := MBasic_momentum hρ hβ
  have := congrArg (fun γ : Occ => γ.sum (fun n m => m • n)) h
  simp only [Legs_mom_add, Legs_mom_single, h1, h2, zero_add] at this
  rw [add_comm p q, add_comm r s]
  exact this.symm

/-- The number of particles in `P_{H,c}` is additive. -/
private lemma Legs_hc_add (ρ L kc : ℝ) (f g : Occ) :
    (f + g).sum (fun n m => if inPHc ρ L kc n then m else 0) =
      f.sum (fun n m => if inPHc ρ L kc n then m else 0) +
        g.sum (fun n m => if inPHc ρ L kc n then m else 0) := by
  refine Finsupp.sum_add_index' (fun n => ?_) (fun n a b => ?_)
  · by_cases hn : inPHc ρ L kc n <;> simp [hn]
  · by_cases hn : inPHc ρ L kc n <;> simp [hn]

private lemma Legs_hc_single (ρ L kc : ℝ) (n : Idx) :
    (Finsupp.single n 1 : Occ).sum (fun n m => if inPHc ρ L kc n then m else 0) =
      if inPHc ρ L kc n then 1 else 0 := by
  rw [Finsupp.sum_single_index]
  by_cases hn : inPHc ρ L kc n <;> simp [hn]

/-- The number of legs in `P_{H,c}` is even (Lemma 8.1 [posscombone0]). -/
private lemma Legs_parity (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1) :
    Even ((if inPHc ρ L kc p then 1 else 0) + (if inPHc ρ L kc q then 1 else 0) +
      (if inPHc ρ L kc r then 1 else 0) + (if inPHc ρ L kc s then 1 else 0)) := by
  obtain ⟨a, ha⟩ := MBasic_PHc_even hρ hα
  obtain ⟨b, hb⟩ := MBasic_PHc_even hρ hβ
  have := congrArg
    (fun γ : Occ => γ.sum fun n m => if inPHc ρ L kc n then m else 0) h
  simp only [Legs_hc_add, Legs_hc_single, ha, hb] at this
  exact ⟨a + (if inPHc ρ L kc r then 1 else 0) + (if inPHc ρ L kc s then 1 else 0) - b, by
    split_ifs at this ⊢ <;> omega⟩

/-- Elements of `M` are symmetric on `P_I` and on `P_H` above `k_c`. -/
private lemma Legs_far_symm (hρ : 0 < ρ) {γ : Occ} (hγ : InM ρ L kc N γ) {x : Idx}
    (hx : inPI ρ L x ∨ (inPH ρ L x ∧ kc < ‖mom L x‖)) : γ x = γ (-x) := by
  rcases hx with h | ⟨h, hk⟩
  · exact MBasic_PI_symm hρ hγ h
  · exact MBasic_PH_far_symm hρ hγ h hk

/-- The created leg `q` is not in `P_I ∪ (P_H ∖ P_{H,c})`. -/
private lemma Legs_not_far_q (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hq0 : q ≠ 0) (hqr : q ≠ r) (hqs : q ≠ s) (hpq : p + q ≠ 0) :
    ¬ (inPI ρ L q ∨ (inPH ρ L q ∧ kc < ‖mom L q‖)) := by
  intro hx
  have e1 := Legs_id_apply h q
  have e2 := Legs_id_apply h (-q)
  have sa := Legs_far_symm hρ hα hx
  have sb := Legs_far_symm hρ hβ hx
  have h1 : q ≠ -q := (Legs_neg_ne_self hq0).symm
  have h2 : p ≠ -q := fun e => hpq (by rw [e]; exact neg_add_cancel q)
  simp [hqr.symm, hqs.symm, h1, h2] at e1 e2
  split_ifs at e1 e2 <;> omega

/-- The created leg `p` is not in `P_I ∪ (P_H ∖ P_{H,c})`. -/
private lemma Legs_not_far_p (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hp0 : p ≠ 0) (hpr : p ≠ r) (hps : p ≠ s) (hpq : p + q ≠ 0) :
    ¬ (inPI ρ L p ∨ (inPH ρ L p ∧ kc < ‖mom L p‖)) := by
  intro hx
  have e1 := Legs_id_apply h p
  have e2 := Legs_id_apply h (-p)
  have sa := Legs_far_symm hρ hα hx
  have sb := Legs_far_symm hρ hβ hx
  have h1 : p ≠ -p := (Legs_neg_ne_self hp0).symm
  have h2 : q ≠ -p := fun e => hpq (by rw [e]; exact add_neg_cancel p)
  simp [hpr.symm, hps.symm, h1, h2] at e1 e2
  split_ifs at e1 e2 <;> omega

/-- The annihilated leg `r` is not in `P_I ∪ (P_H ∖ P_{H,c})`. -/
private lemma Legs_not_far_r (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hr0 : r ≠ 0) (hpr : p ≠ r) (hqr : q ≠ r) (hrs : r + s ≠ 0) :
    ¬ (inPI ρ L r ∨ (inPH ρ L r ∧ kc < ‖mom L r‖)) := by
  intro hx
  have e1 := Legs_id_apply h r
  have e2 := Legs_id_apply h (-r)
  have sa := Legs_far_symm hρ hα hx
  have sb := Legs_far_symm hρ hβ hx
  have h1 : r ≠ -r := (Legs_neg_ne_self hr0).symm
  have h2 : s ≠ -r := fun e => hrs (by rw [e]; exact add_neg_cancel r)
  simp [hpr, hqr, h1, h2] at e1 e2
  split_ifs at e1 e2 <;> omega

/-- The annihilated leg `s` is not in `P_I ∪ (P_H ∖ P_{H,c})`. -/
private lemma Legs_not_far_s (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hs0 : s ≠ 0) (hps : p ≠ s) (hqs : q ≠ s) (hrs : r + s ≠ 0) :
    ¬ (inPI ρ L s ∨ (inPH ρ L s ∧ kc < ‖mom L s‖)) := by
  intro hx
  have e1 := Legs_id_apply h s
  have e2 := Legs_id_apply h (-s)
  have sa := Legs_far_symm hρ hα hx
  have sb := Legs_far_symm hρ hβ hx
  have h1 : s ≠ -s := (Legs_neg_ne_self hs0).symm
  have h2 : r ≠ -s := fun e => hrs (by rw [e]; exact neg_add_cancel s)
  simp [hps, hqs, h1, h2] at e1 e2
  split_ifs at e1 e2 <;> omega

/-- A nonzero leg in the support of an element of `M` and outside `P_I ∪ (P_H ∖ P_{H,c})`
lies in `P_L ∪ P_{H,c}`. -/
private lemma Legs_PL_or_PHc {γ : Occ} (hγ : InM ρ L kc N γ) {x : Idx}
    (hx0 : x ≠ 0) (hx : γ x ≠ 0)
    (hnf : ¬ (inPI ρ L x ∨ (inPH ρ L x ∧ kc < ‖mom L x‖))) :
    inPL ρ L x ∨ inPHc ρ L kc x := by
  rcases MBasic_support hγ x hx with h | h | h | h
  · exact absurd h hx0
  · exact Or.inl h
  · exact absurd (Or.inl h) hnf
  · exact Or.inr ⟨h, not_lt.mp fun hk => hnf (Or.inr ⟨h, hk⟩)⟩

/-- The legs `q, r, s` of a nonzero matrix element lie in `P_L ∪ P_{H,c}`; momentum is conserved
and the number of legs in `P_{H,c}` is even. -/
private lemma Legs_cls_qrs (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) {p q r s : Idx} (hne : (a4 p q r s β).1 ≠ 0)
    (heq : (a4 p q r s β).2 = α) (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hpq : p + q ≠ 0) :
    p + q = r + s ∧ (inPL ρ L q ∨ inPHc ρ L kc q) ∧ (inPL ρ L r ∨ inPHc ρ L kc r) ∧
      (inPL ρ L s ∨ inPHc ρ L kc s) ∧
      Even ((if inPHc ρ L kc p then 1 else 0) + (if inPHc ρ L kc q then 1 else 0) +
        (if inPHc ρ L kc r then 1 else 0) + (if inPHc ρ L kc s then 1 else 0)) := by
  obtain ⟨h1, h2, h3, h4, h⟩ := Legs_a4_id hne heq
  have hm := Legs_mom hρ hα hβ h
  have hrs : r + s ≠ 0 := hm ▸ hpq
  refine ⟨hm, ?_, ?_, ?_, Legs_parity hρ hα hβ h⟩
  · exact Legs_PL_or_PHc hα hq0 (by omega) (Legs_not_far_q hρ hα hβ h hq0 hqr hqs hpq)
  · exact Legs_PL_or_PHc hβ hr0 (by omega) (Legs_not_far_r hρ hα hβ h hr0 hpr hqr hrs)
  · exact Legs_PL_or_PHc hβ hs0 (by omega) (Legs_not_far_s hρ hα hβ h hs0 hps hqs hrs)

/-- The leg `p` of a nonzero matrix element lies in `P_L ∪ P_{H,c}`. -/
private lemma Legs_cls_p (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) {p q r s : Idx} (hne : (a4 p q r s β).1 ≠ 0)
    (heq : (a4 p q r s β).2 = α) (hp0 : p ≠ 0) (hpr : p ≠ r) (hps : p ≠ s) (hpq : p + q ≠ 0) :
    inPL ρ L p ∨ inPHc ρ L kc p := by
  obtain ⟨h1, h2, h3, h4, h⟩ := Legs_a4_id hne heq
  exact Legs_PL_or_PHc hα hp0 (by omega) (Legs_not_far_p hρ hα hβ h hp0 hpr hps hpq)

/-- `P_L` and `P_H` are disjoint and symmetric, so `a ∈ P_L`, `b ∈ P_H` give `a ≠ ±b`. -/
private lemma Legs_pm_PL_PH (hρ : 0 < ρ) {a b : Idx} (ha : inPL ρ L a) (hb : inPH ρ L b) :
    Legs_pm a b :=
  ⟨fun h => Regions_PL_PH hρ ha (h ▸ hb),
    fun h => Regions_PL_PH hρ ha (by rw [h]; exact Regions_PH_neg.2 hb)⟩

/-- If `a = b + c` with `b ∈ P_L` and `c ∈ P_H`, then `a ≠ ±c`. -/
private lemma Legs_pm_L_Hc (hρ : 0 < ρ) {a b c : Idx} (hs : a = b + c) (hb : inPL ρ L b)
    (hc : inPH ρ L c) : Legs_pm a c := by
  refine ⟨fun e => Regions_PL_ne_zero hρ hb ?_, fun e => Regions_PH_two hρ hc ?_⟩
  · rw [e] at hs
    simpa using hs.symm
  · have hb' : b = -(c + c) := by
      have h := hs.symm.trans e
      calc b = (b + c) - c := by abel
        _ = -c - c := by rw [h]
        _ = -(c + c) := by abel
    exact Regions_PL_neg.1 (hb' ▸ hb)

/-- If `a = b + c` with `a ∈ P_L` and `b, c ∈ P_H`, then `b ≠ ±c`. -/
private lemma Legs_pm_Hc_Hc (hρ : 0 < ρ) {a b c : Idx} (hs : a = b + c) (ha : inPL ρ L a)
    (hb : inPH ρ L b) : Legs_pm b c := by
  refine ⟨fun e => Regions_PH_two hρ hb ?_, fun e => Regions_PL_ne_zero hρ ha ?_⟩
  · rw [e] at hs ⊢
    rw [← hs]
    exact ha
  · rw [hs, e]
    simp

/-- At a leg `x ∈ P_L`, `|α(x) - α(-x)| + |β(x) - β(-x)| = 1` when `α - β` equals `±1` at `x`
and `0` at `-x`. -/
private lemma Legs_dsum (hρ : 0 < ρ) {α β : Occ} (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    {x : Idx} (hx : inPL ρ L x) (e1 : α x = β x + 1 ∨ α x + 1 = β x) (e2 : α (-x) = β (-x)) :
    Int.natAbs ((α x : ℤ) - α (-x)) + Int.natAbs ((β x : ℤ) - β (-x)) = 1 := by
  have a1 := MStar_PL_star hρ hα hx
  have a2 := MStar_PL_star hρ hα (Regions_PL_neg.2 hx)
  have b1 := MStar_PL_star hρ hβ hx
  have b2 := MStar_PL_star hρ hβ (Regions_PL_neg.2 hx)
  simp only [alphaStar, neg_neg] at a1 a2 b1 b2
  omega

/-- `F(α) + F(β)` counts the legs in `P_L` when each of them has `α - β = ±1` at `x` and `0`
at `-x`. -/
private lemma Legs_Fal_sum (hρ : 0 < ρ) {n : ℕ} (v : Fin n → Idx) {α β : Occ}
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (h : ∀ i, inPL ρ L (v i) →
      (α (v i) = β (v i) + 1 ∨ α (v i) + 1 = β (v i)) ∧ α (-(v i)) = β (-(v i))) :
    Fal ρ L v α + Fal ρ L v β = (Finset.univ.filter (fun i => inPL ρ L (v i))).card := by
  unfold Fal
  rw [← Finset.sum_add_distrib, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : inPL ρ L (v i)
  · simp only [hi, ite_true]
    exact Legs_dsum hρ hα hβ hi (h i hi).1 (h i hi).2
  · simp [hi]

/-- Value of `α - β` at the created leg `p` when `p` is not `±` another leg. -/
private lemma Legs_nu_p {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hp0 : p ≠ 0) (hpq : p ≠ q) (hpq' : p ≠ -q) (hpr : p ≠ r) (hpr' : p ≠ -r) (hps : p ≠ s)
    (hps' : p ≠ -s) :
    (α p = β p + 1 ∨ α p + 1 = β p) ∧ α (-p) = β (-p) := by
  have e1 := Legs_id_apply h p
  have e2 := Legs_id_apply h (-p)
  have h1 : p ≠ -p := (Legs_neg_ne_self hp0).symm
  have hq : q ≠ -p := fun e => hpq' (by rw [e, neg_neg])
  have hr : r ≠ -p := fun e => hpr' (by rw [e, neg_neg])
  have hs : s ≠ -p := fun e => hps' (by rw [e, neg_neg])
  simp [hpq.symm, hpr.symm, hps.symm, h1, hq, hr, hs] at e1 e2
  refine ⟨Or.inl ?_, ?_⟩ <;> omega

/-- Value of `α - β` at the created leg `q` when `q` is not `±` another leg. -/
private lemma Legs_nu_q {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hq0 : q ≠ 0) (hqp : q ≠ p) (hqp' : q ≠ -p) (hqr : q ≠ r) (hqr' : q ≠ -r) (hqs : q ≠ s)
    (hqs' : q ≠ -s) :
    (α q = β q + 1 ∨ α q + 1 = β q) ∧ α (-q) = β (-q) := by
  have e1 := Legs_id_apply h q
  have e2 := Legs_id_apply h (-q)
  have h1 : q ≠ -q := (Legs_neg_ne_self hq0).symm
  have hp : p ≠ -q := fun e => hqp' (by rw [e, neg_neg])
  have hr : r ≠ -q := fun e => hqr' (by rw [e, neg_neg])
  have hs : s ≠ -q := fun e => hqs' (by rw [e, neg_neg])
  simp [hqp.symm, hqr.symm, hqs.symm, h1, hp, hr, hs] at e1 e2
  refine ⟨Or.inl ?_, ?_⟩ <;> omega

/-- Value of `α - β` at the annihilated leg `r` when `r` is not `±` another leg. -/
private lemma Legs_nu_r {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hr0 : r ≠ 0) (hrp : r ≠ p) (hrp' : r ≠ -p) (hrq : r ≠ q) (hrq' : r ≠ -q) (hrs : r ≠ s)
    (hrs' : r ≠ -s) :
    (α r = β r + 1 ∨ α r + 1 = β r) ∧ α (-r) = β (-r) := by
  have e1 := Legs_id_apply h r
  have e2 := Legs_id_apply h (-r)
  have h1 : r ≠ -r := (Legs_neg_ne_self hr0).symm
  have hp : p ≠ -r := fun e => hrp' (by rw [e, neg_neg])
  have hq : q ≠ -r := fun e => hrq' (by rw [e, neg_neg])
  have hs : s ≠ -r := fun e => hrs' (by rw [e, neg_neg])
  simp [hrp.symm, hrq.symm, hrs.symm, h1, hp, hq, hs] at e1 e2
  refine ⟨Or.inr ?_, ?_⟩ <;> omega

/-- Value of `α - β` at the annihilated leg `s` when `s` is not `±` another leg. -/
private lemma Legs_nu_s {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hs0 : s ≠ 0) (hsp : s ≠ p) (hsp' : s ≠ -p) (hsq : s ≠ q) (hsq' : s ≠ -q) (hsr : s ≠ r)
    (hsr' : s ≠ -r) :
    (α s = β s + 1 ∨ α s + 1 = β s) ∧ α (-s) = β (-s) := by
  have e1 := Legs_id_apply h s
  have e2 := Legs_id_apply h (-s)
  have h1 : s ≠ -s := (Legs_neg_ne_self hs0).symm
  have hp : p ≠ -s := fun e => hsp' (by rw [e, neg_neg])
  have hq : q ≠ -s := fun e => hsq' (by rw [e, neg_neg])
  have hr : r ≠ -s := fun e => hsr' (by rw [e, neg_neg])
  simp [hsp.symm, hsq.symm, hsr.symm, h1, hp, hq, hr] at e1 e2
  refine ⟨Or.inr ?_, ?_⟩ <;> omega

private lemma Legs_strict_neg (k : Idx) : strictPair (-k) = strictPair k := by
  funext α
  unfold strictPair
  rw [neg_neg, add_right_comm]

private lemma Legs_strict_ne {k n : Idx} (α : Occ) (h0 : n ≠ 0) (h1 : n ≠ k) (h2 : n ≠ -k) :
    strictPair k α n = α n := by
  rw [MBasic_strictPair_apply]
  simp [h0, h1, h2]

private lemma Legs_strict_self {k : Idx} (hk : k ≠ 0) (α : Occ) :
    strictPair k α k = α k + 1 := by
  rw [MBasic_strictPair_apply]
  simp [hk, (Legs_neg_ne_self hk).symm]

private lemma Legs_strict_self_neg {k : Idx} (hk : k ≠ 0) (α : Occ) :
    strictPair k α (-k) = α (-k) + 1 := by
  rw [MBasic_strictPair_apply]
  simp [neg_ne_zero.2 hk, Legs_neg_ne_self hk]

private lemma Legs_strict_zero {k : Idx} (hk : k ≠ 0) {γ α' : Occ} (h : strictPair k γ = α')
    (h2 : 2 ≤ γ 0) : γ 0 = α' 0 + 2 := by
  have := DFunLike.congr_fun h 0
  rw [MBasic_strictPair_apply] at this
  simp [Ne.symm hk, (neg_ne_zero.2 hk).symm] at this
  omega

private lemma Legs_soft_ne {u p₁ p₂ n : Idx} (α : Occ) (h0 : n ≠ 0) (hu : n ≠ u) (h1 : n ≠ p₁)
    (h2 : n ≠ p₂) : softPair u p₁ p₂ α n = α n := by
  rw [MBasic_softPair_apply]
  simp [h0, hu, h1, h2]

private lemma Legs_soft_self {u p₁ p₂ : Idx} (α : Occ) (hu0 : u ≠ 0) (h1 : u ≠ p₁)
    (h2 : u ≠ p₂) : softPair u p₁ p₂ α u = α u - 1 := by
  rw [MBasic_softPair_apply]
  simp [hu0, h1, h2]

/-- A momentum in `P_L` is different from `±k` for `k ∈ P_I ∪ P_H`. -/
private lemma Legs_PL_ne_far (hρ : 0 < ρ) {v k : Idx} (hv : inPL ρ L v)
    (hk : inPI ρ L k ∨ inPH ρ L k) : v ≠ k ∧ v ≠ -k := by
  have key : ∀ x, inPL ρ L x → ¬ (inPI ρ L x ∨ inPH ρ L x) := fun x hx h =>
    h.elim (Regions_PL_PI hx) (Regions_PL_PH hρ hx)
  refine ⟨fun e => key k (e ▸ hv) hk, fun e => key k ?_ hk⟩
  have : inPL ρ L (-k) := e ▸ hv
  exact Regions_PL_neg.1 this

/-- Existence in (7.29) [gammaDaal] for `v ∈ P_L`, by induction on the last creation step of
`α ∈ M`. -/
private lemma Legs_exists_PL (hρ : 0 < ρ) {α : Occ} (hα : InM ρ L kc N α) :
    ∀ w : Idx, inPL ρ L w → 1 ≤ α w → 1 ≤ α (-w) →
      ∃ γ, InM ρ L kc N γ ∧ strictPair w γ = α := by
  induction hα with
  | free =>
    intro w hw h1 _
    simp [Ne.symm (Regions_PL_ne_zero hρ hw)] at h1
  | @strictIH α' k hα' hk h2 ih =>
    intro w hw h1 h2'
    have hw0 := Regions_PL_ne_zero hρ hw
    obtain ⟨hwk, hwk'⟩ := Legs_PL_ne_far hρ hw hk
    have hnk : -w ≠ k := fun e => hwk' (neg_eq_iff_eq_neg.mp e)
    have hnk' : -w ≠ -k := fun e => hwk (neg_inj.mp e)
    rw [Legs_strict_ne α' hw0 hwk hwk'] at h1
    rw [Legs_strict_ne α' (neg_ne_zero.2 hw0) hnk hnk'] at h2'
    obtain ⟨γ', hγ', he⟩ := ih w hw h1 h2'
    have h2γ : 2 ≤ γ' 0 := MBasic_strict_le hρ hγ' (by rw [he]; exact hα')
    have hz := Legs_strict_zero hw0 he h2γ
    refine ⟨strictPair k γ', InM.strictIH hγ' hk (by omega), ?_⟩
    rw [Reorder_strict_strict (by omega), he]
  | @strictL α' k hα' hk hmc h2 ih =>
    intro w hw h1 h2'
    have hw0 := Regions_PL_ne_zero hρ hw
    by_cases hkw : k = w
    · subst hkw
      exact ⟨α', hα', rfl⟩
    by_cases hkw' : k = -w
    · subst hkw'
      exact ⟨α', hα', by rw [Legs_strict_neg]⟩
    have hwk : w ≠ k := fun e => hkw e.symm
    have hwk' : w ≠ -k := fun e => hkw' (by rw [e, neg_neg])
    have hnk : -w ≠ k := fun e => hkw' e.symm
    have hnk' : -w ≠ -k := fun e => hwk (neg_inj.mp e)
    rw [Legs_strict_ne α' hw0 hwk hwk'] at h1
    rw [Legs_strict_ne α' (neg_ne_zero.2 hw0) hnk hnk'] at h2'
    obtain ⟨γ', hγ', he⟩ := ih w hw h1 h2'
    have h2γ : 2 ≤ γ' 0 := MBasic_strict_le hρ hγ' (by rw [he]; exact hα')
    have hz := Legs_strict_zero hw0 he h2γ
    have hk0 := Regions_PL_ne_zero hρ hk
    have e1 : γ' k = α' k := by
      rw [← he]
      exact (Legs_strict_ne γ' hk0 hkw hkw').symm
    have e2 : γ' (-k) = α' (-k) := by
      rw [← he]
      exact (Legs_strict_ne γ' (neg_ne_zero.2 hk0) (fun e => hkw' (neg_eq_iff_eq_neg.mp e))
        (fun e => hkw (neg_inj.mp e))).symm
    have hst : alphaStar γ' k = alphaStar α' k := by
      unfold alphaStar
      rw [e1, e2]
    refine ⟨strictPair k γ', InM.strictL hγ' hk (by rw [hst]; exact hmc) (by omega), ?_⟩
    rw [Reorder_strict_strict (by omega), he]
  | @soft α' u p₁ p₂ hα' hu hsym hs hp₁ hp₂ hk₁ hk₂ h0 hu1 ih =>
    intro w hw h1 h2'
    have hw0 := Regions_PL_ne_zero hρ hw
    have hu0 := Regions_PL_ne_zero hρ hu
    obtain ⟨-, -, -, -, hp1u, hp1u', hp2u, hp2u'⟩ := Regions_soft_distinct hρ hu hp₁ hp₂ hs
    obtain ⟨hwp1, hwp1'⟩ := Legs_pm_PL_PH hρ hw hp₁
    obtain ⟨hwp2, hwp2'⟩ := Legs_pm_PL_PH hρ hw hp₂
    have hnp1 : -w ≠ p₁ := fun e => hwp1' (neg_eq_iff_eq_neg.mp e)
    have hnp2 : -w ≠ p₂ := fun e => hwp2' (neg_eq_iff_eq_neg.mp e)
    by_cases hux : u = w ∨ u = -w
    · have hw' : strictPair w = strictPair u := by
        rcases hux with rfl | rfl
        · rfl
        · exact (Legs_strict_neg w).symm
      have hu12 : 1 ≤ softPair u p₁ p₂ α' u ∧ 1 ≤ softPair u p₁ p₂ α' (-u) := by
        rcases hux with rfl | rfl
        · exact ⟨h1, h2'⟩
        · exact ⟨h2', by rw [neg_neg]; exact h1⟩
      have eu := Legs_soft_self α' hu0 hp1u.symm hp2u.symm
      have eu' := Legs_soft_ne (u := u) (p₁ := p₁) (p₂ := p₂) α' (neg_ne_zero.2 hu0)
        (Legs_neg_ne_self hu0) hp1u'.symm hp2u'.symm
      obtain ⟨γ', hγ', he⟩ := ih u hu (by omega) (by omega)
      have h2γ : 2 ≤ γ' 0 := MBasic_strict_le hρ hγ' (by rw [he]; exact hα')
      have hz := Legs_strict_zero hu0 he h2γ
      have hg1 := DFunLike.congr_fun he u
      rw [Legs_strict_self hu0] at hg1
      have hg2 := DFunLike.congr_fun he (-u)
      rw [Legs_strict_self_neg hu0] at hg2
      refine ⟨softPair u p₁ p₂ γ', InM.soft hγ' hu (by omega) hs hp₁ hp₂ hk₁ hk₂ (by omega)
        (by omega), ?_⟩
      have hc := Reorder_soft_strict (u := u) (p₁ := p₁) (p₂ := p₂) (k := u) (α := γ') hu0
        (by omega) (by omega)
      rw [hw', ← hc, he]
    · obtain ⟨huw, huw'⟩ := not_or.mp hux
      have hnu : -u ≠ w := fun e => huw' (neg_eq_iff_eq_neg.mp e)
      have hnu' : -u ≠ -w := fun e => huw (neg_inj.mp e)
      rw [Legs_soft_ne α' hw0 (Ne.symm huw) hwp1 hwp2] at h1
      rw [Legs_soft_ne α' (neg_ne_zero.2 hw0) (Ne.symm huw') hnp1 hnp2] at h2'
      obtain ⟨γ', hγ', he⟩ := ih w hw h1 h2'
      have h2γ : 2 ≤ γ' 0 := MBasic_strict_le hρ hγ' (by rw [he]; exact hα')
      have hz := Legs_strict_zero hw0 he h2γ
      have hg1 := DFunLike.congr_fun he u
      rw [Legs_strict_ne γ' hu0 huw huw'] at hg1
      have hg2 := DFunLike.congr_fun he (-u)
      rw [Legs_strict_ne γ' (neg_ne_zero.2 hu0) hnu hnu'] at hg2
      refine ⟨softPair u p₁ p₂ γ', InM.soft hγ' hu (by omega) hs hp₁ hp₂ hk₁ hk₂ (by omega)
        (by omega), ?_⟩
      have hc := Reorder_soft_strict (u := u) (p₁ := p₁) (p₂ := p₂) (k := w) (α := γ') hu0
        (by omega) (by omega)
      rw [← hc, he]

/-- The unique `γ ∈ M` with `𝓐^v γ = α`, (7.29) [gammaDaal]. -/
theorem Legs_unique_gamma (hρ : 0 < ρ) {v : Idx} (hv : inPL ρ L v ∨ inPI ρ L v)
    {α : Occ} (hα : InM ρ L kc N α) (h1 : 1 ≤ α v) (h2 : 1 ≤ α (-v)) :
    ∃! γ, InM ρ L kc N γ ∧ strictPair v γ = α := by
  have hex : ∃ γ, InM ρ L kc N γ ∧ strictPair v γ = α := by
    rcases hv with hv | hv
    · exact Legs_exists_PL hρ hα v hv h1 h2
    · obtain ⟨β, hβ, -, he, -⟩ := Prop5_2 hρ hv hα h1
      exact ⟨β, hβ, he⟩
  obtain ⟨γ, hγ, he⟩ := hex
  refine ⟨γ, ⟨hγ, he⟩, ?_⟩
  rintro γ₂ ⟨hγ₂, he₂⟩
  have h2γ : 2 ≤ γ 0 := MBasic_strict_le hρ hγ (by rw [he]; exact hα)
  have h2γ₂ : 2 ≤ γ₂ 0 := MBasic_strict_le hρ hγ₂ (by rw [he₂]; exact hα)
  exact Reorder_strictPair_injOn v h2γ₂ h2γ (he₂.trans he.symm)

/-- Lemma 8.1 [posscombone0]; `⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ ≠ 0`. -/
theorem Lemma8_1 (hρ : 0 < ρ) {α β : Occ} {v₁ v₂ v₃ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hne : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) (heq : (a4 0 v₁ v₂ v₃ β).2 = α) :
    (inPL ρ L v₁ ∧ inPHc ρ L kc v₂ ∧ inPHc ρ L kc v₃ ∧
      Legs_pm v₁ v₂ ∧ Legs_pm v₁ v₃ ∧ Legs_pm v₂ v₃) ∨
    (((inPHc ρ L kc v₁ ∧ inPL ρ L v₂ ∧ inPHc ρ L kc v₃) ∨
      (inPHc ρ L kc v₁ ∧ inPHc ρ L kc v₂ ∧ inPL ρ L v₃)) ∧
      Legs_pm v₁ v₂ ∧ Legs_pm v₁ v₃ ∧ Legs_pm v₂ v₃) ∨
    (inPL ρ L v₁ ∧ inPL ρ L v₂ ∧ inPL ρ L v₃) := by
  obtain ⟨-, -, -, -, hid⟩ := Legs_a4_id hne heq
  have hm : v₁ = v₂ + v₃ := by simpa using Legs_mom hρ hα hβ hid
  have hqr : v₁ ≠ v₂ := fun e => h₃ (by rw [e] at hm; simpa using hm.symm)
  have hqs : v₁ ≠ v₃ := fun e => h₂ (by rw [e] at hm; simpa using hm.symm)
  obtain ⟨-, hc1, hc2, hc3, hpar⟩ := Legs_cls_qrs hρ hα hβ hne heq h₁ h₂ h₃ h₂.symm h₃.symm
    hqr hqs (by simpa using h₁)
  have h0 : ¬ inPHc ρ L kc 0 := fun h => Regions_PH_ne_zero hρ h.1 rfl
  obtain ⟨k, hk⟩ := hpar
  simp only [h0, ite_false, zero_add] at hk
  have l1 : ¬ inPHc ρ L kc v₁ → inPL ρ L v₁ := fun h => hc1.resolve_right h
  have l2 : ¬ inPHc ρ L kc v₂ → inPL ρ L v₂ := fun h => hc2.resolve_right h
  have l3 : ¬ inPHc ρ L kc v₃ → inPL ρ L v₃ := fun h => hc3.resolve_right h
  by_cases b1 : inPHc ρ L kc v₁ <;> by_cases b2 : inPHc ρ L kc v₂ <;>
    by_cases b3 : inPHc ρ L kc v₃ <;> simp only [b1, b2, b3, ite_true, ite_false] at hk <;>
    try omega
  · exact Or.inr (Or.inl ⟨Or.inr ⟨b1, b2, l3 b3⟩,
      Legs_pm_L_Hc hρ (by rw [hm, add_comm]) (l3 b3) b2.1,
      Legs_pm_symm (Legs_pm_PL_PH hρ (l3 b3) b1.1),
      Legs_pm_symm (Legs_pm_PL_PH hρ (l3 b3) b2.1)⟩)
  · exact Or.inr (Or.inl ⟨Or.inl ⟨b1, l2 b2, b3⟩,
      Legs_pm_symm (Legs_pm_PL_PH hρ (l2 b2) b1.1),
      Legs_pm_L_Hc hρ hm (l2 b2) b3.1,
      Legs_pm_PL_PH hρ (l2 b2) b3.1⟩)
  · exact Or.inl ⟨l1 b1, b2, b3, Legs_pm_PL_PH hρ (l1 b1) b2.1, Legs_pm_PL_PH hρ (l1 b1) b3.1,
      Legs_pm_Hc_Hc hρ hm (l1 b1) b2.1⟩
  · exact Or.inr (Or.inr ⟨l1 b1, l2 b2, l3 b3⟩)

/-- (8.10) [fab=no] of Lemma 8.2 [FalFbe0]. -/
theorem Lemma8_2_F (hρ : 0 < ρ) {α β : Occ} {v₁ v₂ v₃ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₁₂ : Legs_pm v₁ v₂) (h₁₃ : Legs_pm v₁ v₃) (h₂₃ : Legs_pm v₂ v₃)
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hne : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) (heq : (a4 0 v₁ v₂ v₃ β).2 = α) :
    Fal ρ L ![v₁, v₂, v₃] α + Fal ρ L ![v₁, v₂, v₃] β =
      (Finset.univ.filter (fun i => inPL ρ L (![v₁, v₂, v₃] i))).card := by
  obtain ⟨-, -, -, -, hid⟩ := Legs_a4_id hne heq
  have h1' : v₁ ≠ -0 := by simpa using h₁
  have h2' : v₂ ≠ -0 := by simpa using h₂
  have h3' : v₃ ≠ -0 := by simpa using h₃
  refine Legs_Fal_sum hρ ![v₁, v₂, v₃] hα hβ ?_
  intro i _
  fin_cases i
  · exact Legs_nu_q hid h₁ h₁ h1' h₁₂.1 h₁₂.2 h₁₃.1 h₁₃.2
  · exact Legs_nu_r hid h₂ h₂ h2' (Legs_pm_symm h₁₂).1 (Legs_pm_symm h₁₂).2 h₂₃.1 h₂₃.2
  · exact Legs_nu_s hid h₃ h₃ h3' (Legs_pm_symm h₁₃).1 (Legs_pm_symm h₁₃).2
      (Legs_pm_symm h₂₃).1 (Legs_pm_symm h₂₃).2

/-- Lemma 9.1 [fourlegslemma1], classification, with the case `v₁, v₂ ∈ P_{H,c}`,
`v₃, v₄ ∈ P_L` included. -/
theorem Lemma9_1 (hρ : 0 < ρ) {α β : Occ} {v₁ v₂ v₃ v₄ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₄ : v₄ ≠ 0) (h₁₂ : v₁ + v₂ ≠ 0) (h₁₃ : v₁ ≠ v₃) (h₁₄ : v₁ ≠ v₄)
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hne : (a4 v₁ v₂ v₃ v₄ β).1 ≠ 0) (heq : (a4 v₁ v₂ v₃ v₄ β).2 = α) :
    (inPL ρ L v₁ ∧ inPL ρ L v₂ ∧ inPL ρ L v₃ ∧ inPL ρ L v₄) ∨
    (inPL ρ L v₁ ∧ inPL ρ L v₂ ∧ inPHc ρ L kc v₃ ∧ inPHc ρ L kc v₄) ∨
    (inPHc ρ L kc v₁ ∧ inPHc ρ L kc v₂ ∧ inPL ρ L v₃ ∧ inPL ρ L v₄) ∨
    (((inPL ρ L v₁ ∧ inPHc ρ L kc v₂) ∨ (inPHc ρ L kc v₁ ∧ inPL ρ L v₂)) ∧
      ((inPL ρ L v₃ ∧ inPHc ρ L kc v₄) ∨ (inPHc ρ L kc v₃ ∧ inPL ρ L v₄))) ∨
    (inPHc ρ L kc v₁ ∧ inPHc ρ L kc v₂ ∧ inPHc ρ L kc v₃ ∧ inPHc ρ L kc v₄) := by
  obtain ⟨-, -, -, -, hid⟩ := Legs_a4_id hne heq
  have hm : v₁ + v₂ = v₃ + v₄ := Legs_mom hρ hα hβ hid
  have hqr : v₂ ≠ v₃ := fun e => h₁₄ (by rw [e, add_comm v₃ v₄] at hm; exact add_right_cancel hm)
  have hqs : v₂ ≠ v₄ := fun e => h₁₃ (by rw [e] at hm; exact add_right_cancel hm)
  obtain ⟨-, hc2, hc3, hc4, hpar⟩ := Legs_cls_qrs hρ hα hβ hne heq h₂ h₃ h₄ h₁₃ h₁₄ hqr hqs h₁₂
  have hc1 := Legs_cls_p hρ hα hβ hne heq h₁ h₁₃ h₁₄ h₁₂
  obtain ⟨k, hk⟩ := hpar
  have l1 : ¬ inPHc ρ L kc v₁ → inPL ρ L v₁ := fun h => hc1.resolve_right h
  have l2 : ¬ inPHc ρ L kc v₂ → inPL ρ L v₂ := fun h => hc2.resolve_right h
  have l3 : ¬ inPHc ρ L kc v₃ → inPL ρ L v₃ := fun h => hc3.resolve_right h
  have l4 : ¬ inPHc ρ L kc v₄ → inPL ρ L v₄ := fun h => hc4.resolve_right h
  by_cases b1 : inPHc ρ L kc v₁ <;> by_cases b2 : inPHc ρ L kc v₂ <;>
    by_cases b3 : inPHc ρ L kc v₃ <;> by_cases b4 : inPHc ρ L kc v₄ <;>
    simp only [b1, b2, b3, b4, ite_true, ite_false] at hk <;> try omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b1, b2, b3, b4⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨b1, b2, l3 b3, l4 b4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨b1, l2 b2⟩, Or.inr ⟨b3, l4 b4⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨b1, l2 b2⟩, Or.inl ⟨l3 b3, b4⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨l1 b1, b2⟩, Or.inr ⟨b3, l4 b4⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨l1 b1, b2⟩, Or.inl ⟨l3 b3, b4⟩⟩)))
  · exact Or.inr (Or.inl ⟨l1 b1, l2 b2, b3, b4⟩)
  · exact Or.inl ⟨l1 b1, l2 b2, l3 b3, l4 b4⟩

/-- `F(α) + F(β)` for four legs (Lemma 9.1 [fourlegslemma1]). -/
theorem Lemma9_1_F (hρ : 0 < ρ) {α β : Occ} {v : Fin 4 → Idx} (h0 : ∀ i, v i ≠ 0)
    (hpm : ∀ i j, i ≠ j → Legs_pm (v i) (v j))
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hne : (a4 (v 0) (v 1) (v 2) (v 3) β).1 ≠ 0) (heq : (a4 (v 0) (v 1) (v 2) (v 3) β).2 = α) :
    Fal ρ L v α + Fal ρ L v β = (Finset.univ.filter (fun i => inPL ρ L (v i))).card := by
  obtain ⟨-, -, -, -, hid⟩ := Legs_a4_id hne heq
  refine Legs_Fal_sum hρ v hα hβ ?_
  intro i _
  fin_cases i
  · exact Legs_nu_p hid (h0 0) (hpm 0 1 (by decide)).1 (hpm 0 1 (by decide)).2
      (hpm 0 2 (by decide)).1 (hpm 0 2 (by decide)).2 (hpm 0 3 (by decide)).1
      (hpm 0 3 (by decide)).2
  · exact Legs_nu_q hid (h0 1) (hpm 1 0 (by decide)).1 (hpm 1 0 (by decide)).2
      (hpm 1 2 (by decide)).1 (hpm 1 2 (by decide)).2 (hpm 1 3 (by decide)).1
      (hpm 1 3 (by decide)).2
  · exact Legs_nu_r hid (h0 2) (hpm 2 0 (by decide)).1 (hpm 2 0 (by decide)).2
      (hpm 2 1 (by decide)).1 (hpm 2 1 (by decide)).2 (hpm 2 3 (by decide)).1
      (hpm 2 3 (by decide)).2
  · exact Legs_nu_s hid (h0 3) (hpm 3 0 (by decide)).1 (hpm 3 0 (by decide)).2
      (hpm 3 1 (by decide)).1 (hpm 3 1 (by decide)).2 (hpm 3 2 (by decide)).1
      (hpm 3 2 (by decide)).2

/-- (10.9) [11.1]. -/
theorem Eq10_9 (hρ : 0 < ρ) {α β γ : Occ} {k₁ k₂ k₃ k₄ : Idx} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N β) (hγ : InM ρ L kc N γ)
    (hne : (a4 k₁ k₂ k₃ k₄ γ).1 ≠ 0) (heq : (a4 k₁ k₂ k₃ k₄ γ).2 = β) :
    k₁ + k₂ = k₃ + k₄ ∧
      (softPair (k₁ + k₂) k₁ k₂ α = β ↔ softPair (k₃ + k₄) k₃ k₄ α = γ) := by
  have _hα := hα
  obtain ⟨-, -, -, -, hid⟩ := Legs_a4_id hne heq
  have hm := Legs_mom hρ hβ hγ hid
  refine ⟨hm, ?_⟩
  rw [← hm]
  unfold softPair
  generalize α - Finsupp.single 0 1 - Finsupp.single (k₁ + k₂) 1 = A
  constructor
  · intro h
    refine add_right_cancel (b := Finsupp.single k₂ 1 + Finsupp.single k₁ 1) ?_
    calc A + Finsupp.single k₃ 1 + Finsupp.single k₄ 1 +
          (Finsupp.single k₂ 1 + Finsupp.single k₁ 1)
        = (A + Finsupp.single k₁ 1 + Finsupp.single k₂ 1) + Finsupp.single k₄ 1 +
          Finsupp.single k₃ 1 := by abel
      _ = β + Finsupp.single k₄ 1 + Finsupp.single k₃ 1 := by rw [h]
      _ = γ + Finsupp.single k₂ 1 + Finsupp.single k₁ 1 := hid
      _ = γ + (Finsupp.single k₂ 1 + Finsupp.single k₁ 1) := by abel
  · intro h
    refine add_right_cancel (b := Finsupp.single k₄ 1 + Finsupp.single k₃ 1) ?_
    calc A + Finsupp.single k₁ 1 + Finsupp.single k₂ 1 +
          (Finsupp.single k₄ 1 + Finsupp.single k₃ 1)
        = (A + Finsupp.single k₃ 1 + Finsupp.single k₄ 1) + Finsupp.single k₂ 1 +
          Finsupp.single k₁ 1 := by abel
      _ = γ + Finsupp.single k₂ 1 + Finsupp.single k₁ 1 := by rw [h]
      _ = β + Finsupp.single k₄ 1 + Finsupp.single k₃ 1 := hid.symm
      _ = β + (Finsupp.single k₄ 1 + Finsupp.single k₃ 1) := by abel

end Legs

end LHYUpper
