module

public import LHYUpper.Particles.UpperIH
public import LHYUpper.Particles.UpperL
public import LHYUpper.Riemann.ScaledLimits

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Particle numbers in the regions: Proposition 5.4

Bounds the particle numbers `Σ Q_Ψ` over the regions `P_I`, `P_H` and `P_L` of Definition 3.1 [def1]
(Proposition 5.4 [particlebound]): (5.29) [temp4.17] as `Prop5_4_PI`, (5.30) [4.18] as `Prop5_4_PH`
and `Prop5_4_PH_paper`, and (5.31) [4.19] as `Prop5_4_PL`. From these and `N - Q_Ψ(0) = Σ_{P_I} Q_Ψ
+ Σ_{P_H} Q_Ψ + Σ_{P_L} Q_Ψ` it derives (5.32) [resultlbpsi0] as `Eq5_32`, the lower bound of Lemma
5.3 [boundspsi0] with a rate. -/

/-- For all large `N`: `N ≥ 1`, `ρ_N ≤ ρ₁` and `2π ≤ L_N ρ_N^{1/2}`. -/
private lemma Totals_eventually {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ rhoN N ≤ ρ₁ ∧ 2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hP : ∀ {a : ℝ}, 0 < a → Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
    intro a ha
    have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.comp hT
  have h1 : ∀ᶠ N : ℕ in atTop, rhoN N ≤ ρ₁ := hT.eventually (ge_mem_nhds hρ₁)
  have h2 : ∀ᶠ N : ℕ in atTop, 2 * π * rhoN N ^ (13 / 24 : ℝ) ≤ 1 := by
    have h := (hP (by norm_num : (0 : ℝ) < 13 / 24)).const_mul (2 * π)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 1, h1, h2] with N hN hρ₁N hΔ
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  refine ⟨hN, hρ₁N, ?_⟩
  have hq : 0 < rhoN N ^ (13 / 24 : ℝ) := Real.rpow_pos_of_pos hρ _
  have e : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) = 1 := by
    rw [LN, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  by_contra h
  have h' : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) <
      2 * π * rhoN N ^ (13 / 24 : ℝ) := mul_lt_mul_of_pos_right (not_le.1 h) hq
  linarith

/-- `L ρ^{1/2} = ρ^{-13/24}` at `L = L_N`, `ρ = ρ_N`: the shell width is `2π ρ^{13/24}`. -/
private lemma Totals_L_sqrt {N : ℕ} (hρ : 0 < rhoN N) :
    LN N * rhoN N ^ (1 / 2 : ℝ) = (rhoN N ^ (13 / 24 : ℝ))⁻¹ := by
  rw [LN, ← Real.rpow_add hρ, ← Real.rpow_neg hρ.le]
  norm_num

/-- `2π ≤ L ρ^{1/2}` implies `2π ≤ L ε` for `ρ ≤ 1`. -/
private lemma Totals_two_pi_eps {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 0 < L)
    (h : 2 * π ≤ L * ρ ^ (1 / 2 : ℝ)) : 2 * π ≤ L * epsP ρ :=
  h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)) hL.le)

/-- `|Re ĝ(p)| ≤ ∫ |g|` for every `V`, `w`. -/
private lemma Totals_re_ft_le (V w : R3 → ℝ) (p : R3) :
    |(ft (gfun V w) p).re| ≤ ∫ x, |gfun V w x| := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold ft
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- A function on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma Totals_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
    (hf : ∀ n, f n ≠ 0 → ‖mom L n‖ ≤ R) : Summable f := by
  have hfin : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
    set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
    refine (Set.finite_Icc (fun _ : Fin 3 => -B) (fun _ => B)).subset ?_
    intro n hn
    have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
      intro i
      have h1 : |(mom L n).ofLp i| ≤ R := by
        have := PiLp.norm_apply_le (mom L n) i
        rw [Real.norm_eq_abs] at this
        exact this.trans hn
      rw [Cells_mom_apply, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
      have h2 : |(n i : ℝ)| ≤ L * R / (2 * π) := by
        rw [le_div_iff₀ (by positivity)]
        have := h1
        rw [div_mul_eq_mul_div, div_le_iff₀ hL] at this
        nlinarith
      exact h2.trans (Int.le_ceil _)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 (hi i)).1
      exact_mod_cast this
    · have := (abs_le.1 (hi i)).2
      exact_mod_cast this
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- `Q_Ψ(n) ≥ 0`. -/
private lemma Totals_Q_nonneg (Ψ : Occ → ℂ) (n : Idx) : 0 ≤ Expect.Q Ψ [n] := by
  unfold Expect.Q
  refine tsum_nonneg fun α => ?_
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  positivity

/-- `Ψ` vanishes off `M`. -/
private lemma Totals_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- For `n ≠ 0` outside `P_L ∪ P_I ∪ P_H`, `Q_Ψ(n) = 0` (`MBasic_support`). -/
private lemma Totals_Q_eq_zero (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {n : Idx} (hn0 : n ≠ 0)
    (hL : ¬ inPL (rhoN N) (LN N) n) (hI : ¬ inPI (rhoN N) (LN N) n)
    (hH : ¬ inPH (rhoN N) (LN N) n) : Expect.Q (trialState V w kc N) [n] = 0 := by
  unfold Expect.Q
  refine (tsum_congr fun α => ?_).trans tsum_zero
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  by_cases hz : ‖trialState V w kc N α‖ ^ 2 = 0
  · rw [hz, mul_zero]
  · have hα := Totals_inM hz
    have : α n = 0 := by
      by_contra h
      rcases MBasic_support hα n h with h0 | h0 | h0 | h0
      · exact hn0 h0
      · exact hL h0
      · exact hI h0
      · exact hH h0
    rw [this]
    simp

/-- Comparison of restricted sums of a nonnegative summable family with a dominating one. -/
private lemma Totals_tsum_ite_le {f d : Idx → ℝ} {P : Idx → Prop} (hf0 : ∀ n, 0 ≤ f n)
    (hfs : Summable f) (hd : Summable fun n => if P n then d n else 0)
    (h : ∀ n, P n → f n ≤ d n) :
    (∑' n, if P n then f n else 0) ≤ ∑' n, if P n then d n else 0 := by
  have hs : Summable fun n => if P n then f n else 0 :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hf0 n])
      (fun n => by split_ifs <;> simp [hf0 n]) hfs
  refine hs.tsum_le_tsum (fun n => ?_) hd
  by_cases hn : P n
  · simp only [hn, ite_true]
    exact h n hn
  · simp [hn]

/-- `N − Q_Ψ(0) = Σ_{P_I} Q_Ψ + Σ_{P_H} Q_Ψ + Σ_{P_L} Q_Ψ`, by `Σ_n Q_Ψ(n) = N` and the support of
`Ψ` in `P` (`MBasic_support`). -/
private lemma Totals_split (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) - Expect.Q (trialState V w kc N) [0] =
      (∑' n : Idx, (if inPI (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) +
      (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) +
      (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  set Q : Idx → ℝ := fun n => Expect.Q (trialState V w kc N) [n] with hQ
  have hs : HasSum Q N := Particles_hasSum_Q V w kc hN
  have hQs : Summable Q := hs.summable
  have hQnn : ∀ n, 0 ≤ Q n := fun n => Totals_Q_nonneg _ n
  have hsub := hs.sub (hasSum_ite_eq (0 : Idx) (Q 0))
  have hsum : ∀ P : Idx → Prop, Summable fun n => if P n then Q n else 0 := fun P =>
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hQnn n])
      (fun n => by split_ifs <;> simp [hQnn n]) hQs
  have hfun : (fun n : Idx => Q n - if n = 0 then Q 0 else 0) =
      fun n => ((if inPI (rhoN N) (LN N) n then Q n else 0) +
        (if inPH (rhoN N) (LN N) n then Q n else 0)) +
        (if inPL (rhoN N) (LN N) n then Q n else 0) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      have h1 : ¬ inPI (rhoN N) (LN N) 0 := fun h => Regions_PI_ne_zero hρ h rfl
      have h2 : ¬ inPH (rhoN N) (LN N) 0 := fun h => Regions_PH_ne_zero hρ h rfl
      have h3 : ¬ inPL (rhoN N) (LN N) 0 := fun h => Regions_PL_ne_zero hρ h rfl
      simp [h1, h2, h3]
    · by_cases hI : inPI (rhoN N) (LN N) n
      · have h2 : ¬ inPH (rhoN N) (LN N) n := Regions_PI_PH hI
        have h3 : ¬ inPL (rhoN N) (LN N) n := fun h => Regions_PL_PI h hI
        simp [hn, hI, h2, h3]
      · by_cases hH : inPH (rhoN N) (LN N) n
        · have h3 : ¬ inPL (rhoN N) (LN N) n := fun h => Regions_PL_PH hρ h hH
          simp [hn, hI, hH, h3]
        · by_cases hL : inPL (rhoN N) (LN N) n
          · simp [hn, hI, hH, hL]
          · have := Totals_Q_eq_zero V w kc N hn hL hI hH
            simp [hn, hI, hH, hL, hQ, this]
  rw [hfun] at hsub
  have hall := ((hsum (inPI (rhoN N) (LN N))).hasSum.add (hsum (inPH (rhoN N) (LN N))).hasSum).add
    (hsum (inPL (rhoN N) (LN N))).hasSum
  exact hsub.unique hall

/-- (5.29) [temp4.17] of Proposition 5.4 [particlebound]. -/
theorem Prop5_4_PI (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPI (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) ≤ C * rhoN N ^ (3/2 + 1/200 : ℝ) := by
  obtain ⟨N₁, h₁⟩ := Lemma5_4_PI V w
  set G₁ := ∫ x, |gfun V w x| with hG₁
  have hG0 : 0 ≤ G₁ := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨K, ρ₁, hK, hρ₁, hsum⟩ := sum_PI_occ (g := G₁ + 1) (by positivity)
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (Totals_eventually hρ₁)
  refine ⟨K, hK, max N₁ N₂, fun N hN kc => ?_⟩
  obtain ⟨hN1, hρle, hL2π⟩ := h₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hgp : ∀ p, |(fun p : R3 => -(ft (gfun V w) p).re) p| ≤ G₁ + 1 := fun p => by
    simp only [abs_neg]
    linarith [Totals_re_ft_le V w p]
  have key := hsum (fun p : R3 => -(ft (gfun V w) p).re) (rhoN N) (LN N) hgp hρ hρle hL2π
  have hQs : Summable (fun n : Idx => Expect.Q (trialState V w kc N) [n]) :=
    (Particles_hasSum_Q V w kc hN1).summable
  have hd : Summable fun n : Idx => if inPI (rhoN N) (LN N) n then
      (rhoN N * (-(ft (gfun V w) (mom (LN N) n)).re) / ‖mom (LN N) n‖ ^ 2) ^ 2 /
        (1 - (rhoN N * (-(ft (gfun V w) (mom (LN N) n)).re) / ‖mom (LN N) n‖ ^ 2) ^ 2)
      else 0 :=
    Totals_summable_ball (R := epsP (rhoN N)) hL _ (fun n hn => by
      by_contra h
      exact hn (by simp [show ¬ inPI (rhoN N) (LN N) n from fun h' => h h'.2]))
  have hle := Totals_tsum_ite_le (P := inPI (rhoN N) (LN N)) (fun n => Totals_Q_nonneg _ n)
    hQs hd (fun n hn => by
      have hnL : ¬ inPL (rhoN N) (LN N) n := fun h => Regions_PL_PI h hn
      have e : rhoN N * lam V w (rhoN N) (LN N) n =
          rhoN N * (-(ft (gfun V w) (mom (LN N) n)).re) / ‖mom (LN N) n‖ ^ 2 := by
        simp only [lam, hnL, ite_false]
        ring
      have := h₁ N (le_of_max_le_left hN) kc n hn
      rwa [e] at this)
  calc (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPI (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))
      ≤ (LN N ^ 3)⁻¹ * ∑' n : Idx, (if inPI (rhoN N) (LN N) n then
          (rhoN N * (-(ft (gfun V w) (mom (LN N) n)).re) / ‖mom (LN N) n‖ ^ 2) ^ 2 /
            (1 - (rhoN N * (-(ft (gfun V w) (mom (LN N) n)).re) / ‖mom (LN N) n‖ ^ 2) ^ 2)
          else 0) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ K * rhoN N ^ (3/2 + 1/200 : ℝ) := key

/-- (5.30) [4.18] of Proposition 5.4 [particlebound], with the rate `ρ^{2−η}`. -/
theorem Prop5_4_PH (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) ≤ C * rhoN N ^ (2 - 1/200 : ℝ) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma5_4_PH V w
  obtain ⟨K₀, hK₀, hK⟩ := sum_norm_rpow_gt (s := 4) (by norm_num)
  set G₁ := ∫ x, |gfun V w x| with hG₁
  have hG0 : 0 ≤ G₁ := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (Totals_eventually one_pos)
  refine ⟨C₁ * G₁ * K₀, by positivity, max N₁ N₂, fun N hN kc => ?_⟩
  obtain ⟨hN1, -, hL2π⟩ := h₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  obtain ⟨hKs, hKb⟩ := hK (LN N) (epsP (rhoN N)) hε (Totals_two_pi_eps hρ hρ1 hL hL2π)
  have hQs : Summable (fun n : Idx => Expect.Q (trialState V w kc N) [n]) :=
    (Particles_hasSum_Q V w kc hN1).summable
  have hdeq : ∀ n : Idx, (if inPH (rhoN N) (LN N) n then
        C₁ * G₁ * rhoN N ^ 2 * ‖mom (LN N) n‖ ^ (-(4 : ℝ)) else 0) =
      C₁ * G₁ * rhoN N ^ 2 * (if epsP (rhoN N) < ‖mom (LN N) n‖ then
        ‖mom (LN N) n‖ ^ (-(4 : ℝ)) else 0) := by
    intro n
    by_cases h : epsP (rhoN N) < ‖mom (LN N) n‖
    · have h' : inPH (rhoN N) (LN N) n := h
      simp [h, h']
    · have h' : ¬ inPH (rhoN N) (LN N) n := h
      simp [h, h']
  have hd : Summable fun n : Idx => if inPH (rhoN N) (LN N) n then
      C₁ * G₁ * rhoN N ^ 2 * ‖mom (LN N) n‖ ^ (-(4 : ℝ)) else 0 := by
    simp_rw [hdeq]
    exact hKs.mul_left _
  have hle := Totals_tsum_ite_le (P := inPH (rhoN N) (LN N)) (fun n => Totals_Q_nonneg _ n)
    hQs hd (fun n hn => by
      have hnL : ¬ inPL (rhoN N) (LN N) n := fun h => Regions_PL_PH hρ h hn
      have hlam := Particles_lam_abs_le V w (rhoN N) (LN N) n hnL
      have hnu : epsP (rhoN N) < ‖mom (LN N) n‖ := hn
      have hnu0 : 0 < ‖mom (LN N) n‖ := hε.trans hnu
      have hq := h₁ N (le_of_max_le_left hN) kc n hn
      have e : ‖mom (LN N) n‖ ^ (-(4 : ℝ)) = (‖mom (LN N) n‖ ^ 4)⁻¹ := by
        rw [Real.rpow_neg hnu0.le]
        norm_cast
      refine hq.trans ?_
      calc C₁ * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) n| / ‖mom (LN N) n‖ ^ 2
          ≤ C₁ * rhoN N ^ 2 * (G₁ / ‖mom (LN N) n‖ ^ 2) / ‖mom (LN N) n‖ ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlam (by positivity)) (by positivity)
        _ = C₁ * G₁ * rhoN N ^ 2 * ‖mom (LN N) n‖ ^ (-(4 : ℝ)) := by
            rw [e]
            field_simp)
  have e2 : rhoN N ^ 2 * epsP (rhoN N) ^ (3 - 4 : ℝ) = rhoN N ^ (2 - 1/200 : ℝ) := by
    rw [epsP, ← Real.rpow_mul hρ.le, ← Real.rpow_natCast, ← Real.rpow_add hρ]
    norm_num
  calc (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))
      ≤ (LN N ^ 3)⁻¹ * ∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          C₁ * G₁ * rhoN N ^ 2 * ‖mom (LN N) n‖ ^ (-(4 : ℝ)) else 0) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C₁ * G₁ * rhoN N ^ 2 * ((LN N ^ 3)⁻¹ * ∑' n : Idx,
          (if epsP (rhoN N) < ‖mom (LN N) n‖ then ‖mom (LN N) n‖ ^ (-(4 : ℝ)) else 0)) := by
        simp_rw [hdeq]
        rw [tsum_mul_left]
        ring
    _ ≤ C₁ * G₁ * rhoN N ^ 2 * (K₀ * epsP (rhoN N) ^ (3 - 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hKb (by positivity)
    _ = C₁ * G₁ * K₀ * (rhoN N ^ 2 * epsP (rhoN N) ^ (3 - 4 : ℝ)) := by ring
    _ = C₁ * G₁ * K₀ * rhoN N ^ (2 - 1/200 : ℝ) := by rw [e2]

/-- (5.30) [4.18] of Proposition 5.4 [particlebound]. -/
theorem Prop5_4_PH_paper (V w : R3 → ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) ≤ rhoN N ^ (7/4 : ℝ) := by
  obtain ⟨C, hC, N₁, h₁⟩ := Prop5_4_PH V w
  have hC1 : 0 < C + 1 := by positivity
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1
    (Totals_eventually (ρ₁ := (C + 1) ^ (-(200 / 49 : ℝ))) (Real.rpow_pos_of_pos hC1 _))
  refine ⟨max N₁ N₂, fun N hN kc => ?_⟩
  obtain ⟨hN1, hρle, -⟩ := h₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have h49 : rhoN N ^ (49 / 200 : ℝ) ≤ (C + 1)⁻¹ := by
    calc rhoN N ^ (49 / 200 : ℝ) ≤ ((C + 1) ^ (-(200 / 49 : ℝ))) ^ (49 / 200 : ℝ) :=
          Real.rpow_le_rpow hρ.le hρle (by norm_num)
      _ = (C + 1)⁻¹ := by
          rw [← Real.rpow_mul hC1.le, show -(200 / 49 : ℝ) * (49 / 200) = -1 by norm_num,
            Real.rpow_neg_one]
  have h1 : C * rhoN N ^ (49 / 200 : ℝ) ≤ 1 := by
    calc C * rhoN N ^ (49 / 200 : ℝ) ≤ (C + 1) * rhoN N ^ (49 / 200 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hρ.le _)
      _ ≤ (C + 1) * (C + 1)⁻¹ := mul_le_mul_of_nonneg_left h49 hC1.le
      _ = 1 := mul_inv_cancel₀ hC1.ne'
  have e : rhoN N ^ (2 - 1/200 : ℝ) = rhoN N ^ (49 / 200 : ℝ) * rhoN N ^ (7 / 4 : ℝ) := by
    rw [← Real.rpow_add hρ]
    norm_num
  calc _ ≤ C * rhoN N ^ (2 - 1/200 : ℝ) := h₁ N (le_of_max_le_left hN) kc
    _ = (C * rhoN N ^ (49 / 200 : ℝ)) * rhoN N ^ (7 / 4 : ℝ) := by rw [e]; ring
    _ ≤ 1 * rhoN N ^ (7 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hρ.le _)
    _ = rhoN N ^ (7 / 4 : ℝ) := one_mul _

/-- (5.31) [4.19] of Proposition 5.4 [particlebound]. -/
theorem Prop5_4_PL {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) ≤
        (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) + C * rhoN N ^ (1/200 : ℝ)) * rhoN N ^ (3/2 : ℝ) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma5_4_PL hg
  obtain ⟨K, hK, hocc⟩ := sum_PL_occ hg
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (Totals_eventually one_pos)
  set G := g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hK' : 0 ≤ K * (1 + 2 * π) := by positivity
  refine ⟨K * (1 + 2 * π) + C₁ * (G + K * (1 + 2 * π)), by positivity, max N₁ N₂,
    fun N hN kc => ?_⟩
  obtain ⟨hN1, -, hL2π⟩ := h₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP (rhoN N) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hQs : Summable (fun n : Idx => Expect.Q (trialState V w kc N) [n]) :=
    (Particles_hasSum_Q V w kc hN1).summable
  -- the error factor `ρ m_c / ε ≤ ε`
  have hc : rhoN N * mc (rhoN N) / epsP (rhoN N) ≤ epsP (rhoN N) := by
    have e : rhoN N * mc (rhoN N) / epsP (rhoN N) = rhoN N ^ (1 - 1/200 - 1/200 : ℝ) := by
      rw [mc, epsP, Real.rpow_sub hρ, Real.rpow_sub hρ, Real.rpow_one, Real.rpow_neg hρ.le]
      have : rhoN N ^ (1/200 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hρ _).ne'
      field_simp
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  set c := C₁ * rhoN N * mc (rhoN N) / epsP (rhoN N) with hcdef
  have hmc : 0 ≤ mc (rhoN N) := Real.rpow_nonneg hρ.le _
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (mul_nonneg hC₁ hρ.le) hmc) hε.le
  have hcle : c ≤ C₁ * epsP (rhoN N) := by
    have : c = C₁ * (rhoN N * mc (rhoN N) / epsP (rhoN N)) := by rw [hcdef]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hc hC₁
  -- the dominating family
  set s : Idx → ℝ := fun n => (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2 /
    (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) with hs
  have hd : Summable fun n : Idx => if inPL (rhoN N) (LN N) n then s n * (1 + c) else 0 :=
    Totals_summable_ball (R := (epsP (rhoN N))⁻¹ * rhoN N ^ (1/2 : ℝ)) hL _ (fun n hn => by
      by_contra h
      exact hn (by simp [show ¬ inPL (rhoN N) (LN N) n from fun h' => h h'.2]))
  have hle := Totals_tsum_ite_le (P := inPL (rhoN N) (LN N)) (fun n => Totals_Q_nonneg _ n)
    hQs hd (fun n hn => h₁ N (le_of_max_le_left hN) kc n hn)
  -- the sum of the pin `sum_PL_occ`
  have hsPL : (∑' n : Idx, if inPL (rhoN N) (LN N) n then s n * (1 + c) else 0) =
      (∑' n : Idx, if inPL (rhoN N) (LN N) n then
        (rhoN N * lamPL (g0 V w) (rhoN N) (mom (LN N) n)) ^ 2 /
          (1 - (rhoN N * lamPL (g0 V w) (rhoN N) (mom (LN N) n)) ^ 2) else 0) * (1 + c) := by
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    by_cases h : inPL (rhoN N) (LN N) n
    · simp only [h, ite_true, hs, lam_of_inPL h]
    · simp [h]
  set S := ∑' n : Idx, if inPL (rhoN N) (LN N) n then
        (rhoN N * lamPL (g0 V w) (rhoN N) (mom (LN N) n)) ^ 2 /
          (1 - (rhoN N * lamPL (g0 V w) (rhoN N) (mom (LN N) n)) ^ 2) else 0 with hSdef
  -- the Riemann-sum pin `sum_PL_occ`, with the shell width `2π ρ^{13/24} ≤ 2π ε`
  have h2π : 2 * π / (LN N * rhoN N ^ (1/2 : ℝ)) ≤ 2 * π * epsP (rhoN N) := by
    rw [Totals_L_sqrt hρ, div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)) (by positivity)
  have hab := (abs_le.1 (hocc (rhoN N) (LN N) hρ hρ1 hL2π)).2
  have hA : (LN N ^ 3)⁻¹ * rhoN N ^ (-(3/2 : ℝ)) * S ≤
      G + K * (1 + 2 * π) * epsP (rhoN N) := by
    have h3 : K * (rhoN N ^ (1/200 : ℝ) + 2 * π / (LN N * rhoN N ^ (1/2 : ℝ))) ≤
        K * (1 + 2 * π) * epsP (rhoN N) :=
      calc _ ≤ K * (epsP (rhoN N) + 2 * π * epsP (rhoN N)) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl h2π) hK
        _ = _ := by ring
    linarith
  have hB : (LN N ^ 3)⁻¹ * S ≤ (G + K * (1 + 2 * π) * epsP (rhoN N)) * rhoN N ^ (3/2 : ℝ) := by
    have e1 : rhoN N ^ (-(3/2 : ℝ)) * rhoN N ^ (3/2 : ℝ) = 1 := by
      rw [← Real.rpow_add hρ]
      norm_num
    calc (LN N ^ 3)⁻¹ * S
        = ((LN N ^ 3)⁻¹ * rhoN N ^ (-(3/2 : ℝ)) * S) * rhoN N ^ (3/2 : ℝ) := by
          calc (LN N ^ 3)⁻¹ * S
              = (LN N ^ 3)⁻¹ * S * (rhoN N ^ (-(3/2 : ℝ)) * rhoN N ^ (3/2 : ℝ)) := by
                rw [e1, mul_one]
            _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hρ.le _)
  have hfin : (G + K * (1 + 2 * π) * epsP (rhoN N)) * (1 + c) ≤
      G + (K * (1 + 2 * π) + C₁ * (G + K * (1 + 2 * π))) * epsP (rhoN N) := by
    have h3 : (G + K * (1 + 2 * π) * epsP (rhoN N)) * (1 + c) ≤
        (G + K * (1 + 2 * π) * epsP (rhoN N)) * (1 + C₁ * epsP (rhoN N)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hC₁ hK') (mul_nonneg hε.le (sub_nonneg.2 hε1))]
  calc (LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))
      ≤ (LN N ^ 3)⁻¹ * ∑' n : Idx, (if inPL (rhoN N) (LN N) n then s n * (1 + c) else 0) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ((LN N ^ 3)⁻¹ * S) * (1 + c) := by rw [hsPL]; ring
    _ ≤ ((G + K * (1 + 2 * π) * epsP (rhoN N)) * rhoN N ^ (3/2 : ℝ)) * (1 + c) :=
        mul_le_mul_of_nonneg_right hB (by linarith)
    _ = ((G + K * (1 + 2 * π) * epsP (rhoN N)) * (1 + c)) * rhoN N ^ (3/2 : ℝ) := by ring
    _ ≤ (G + (K * (1 + 2 * π) + C₁ * (G + K * (1 + 2 * π))) * epsP (rhoN N)) *
          rhoN N ^ (3/2 : ℝ) := mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hρ.le _)

/-- (5.32) [resultlbpsi0]: the lower bound of Lemma 5.3 [boundspsi0] with a rate. -/
theorem Eq5_32 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rho0 (g0 V w) (rhoN N) - C * rhoN N ^ (3/2 + 1/200 : ℝ) ≤
        Expect.Q (trialState V w kc N) [0] / LN N ^ 3 := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Prop5_4_PI V w
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Prop5_4_PH V w
  obtain ⟨C₃, hC₃, N₃, h₃⟩ := Prop5_4_PL hg
  refine ⟨C₁ + C₂ + C₃, by positivity, max (max (max N₁ N₂) N₃) 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hI := h₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    |>.trans hN) kc
  have hH := h₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    |>.trans hN) kc
  have hP := h₃ N (le_trans (le_max_right _ _) (le_max_left _ _) |>.trans hN) kc
  have hsplit := Totals_split V w kc hN1
  set SI := ∑' n : Idx, (if inPI (rhoN N) (LN N) n then
      Expect.Q (trialState V w kc N) [n] else 0) with hSI
  set SH := ∑' n : Idx, (if inPH (rhoN N) (LN N) n then
      Expect.Q (trialState V w kc N) [n] else 0) with hSH
  set SL := ∑' n : Idx, (if inPL (rhoN N) (LN N) n then
      Expect.Q (trialState V w kc N) [n] else 0) with hSL
  have hL3 : 0 < LN N ^ 3 := by positivity
  -- `ρ^{2-η} ≤ ρ^{3/2+η}`
  have h2 : rhoN N ^ (2 - 1/200 : ℝ) ≤ rhoN N ^ (3/2 + 1/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have e1 : rhoN N ^ (1/200 : ℝ) * rhoN N ^ (3/2 : ℝ) = rhoN N ^ (3/2 + 1/200 : ℝ) := by
    rw [mul_comm, ← Real.rpow_add hρ]
  have hQ0 : Expect.Q (trialState V w kc N) [0] = (N : ℝ) - (SI + SH + SL) := by
    rw [← hsplit]
    ring
  have hdiv : Expect.Q (trialState V w kc N) [0] / LN N ^ 3 =
      rhoN N - (LN N ^ 3)⁻¹ * SI - (LN N ^ 3)⁻¹ * SH - (LN N ^ 3)⁻¹ * SL := by
    rw [hQ0, ← hNL]
    field_simp
    ring
  have hrho0 : rho0 (g0 V w) (rhoN N) = rhoN N - g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) *
      rhoN N ^ (3/2 : ℝ) := by
    unfold rho0
    ring
  have hC2 : C₂ * rhoN N ^ (2 - 1/200 : ℝ) ≤ C₂ * rhoN N ^ (3/2 + 1/200 : ℝ) :=
    mul_le_mul_of_nonneg_left h2 hC₂
  rw [hdiv, hrho0]
  nlinarith [hI, hH, hP, hC2, e1]

end LHYUpper
