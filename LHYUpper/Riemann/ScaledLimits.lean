module

public import LHYUpper.Riemann.Scaled
public import LHYUpper.Riemann.Densities

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! # Limits of the Riemann sums over `P_L` and `P_I`

Applies the Riemann-sum lemma on `P_L` to the densities of §5–§7: the occupation sum (5.35)–(5.36)
[3.1, sum] (`sum_PL_occ`), the tail sums of (5.38) [tail], (5.39) [temp6.35], (5.43) [upt01] and
(7.21) [temp8.28] (`sum_PL_tail`), the kinetic sum (6.3) [boundspsiu2PLtotal] (`sum_PL_kin`) and the
potential sum in the proof of (7.8) [u-uPL] and of (7.67) [temp8.75] (`sum_PL_pot`). Also gives the
`P_I` sum in the proof of (5.29) [temp4.17] and the replacement `ρ₀ w_u → ρ g₀ |u|^{-2}` on `P_L` in
the proof of (6.3). -/

private lemma ScaledLimits_sqrt_sq {ρ : ℝ} (hρ : 0 < ρ) : (ρ ^ (1/2 : ℝ)) ^ 2 = ρ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

/-- `‖u‖² = ρ ‖ρ^{-1/2} u‖²`. -/
private lemma ScaledLimits_norm_sq {ρ : ℝ} (hρ : 0 < ρ) (u : R3) :
    ‖u‖ ^ 2 = ρ * ‖(ρ ^ (1/2 : ℝ))⁻¹ • u‖ ^ 2 := by
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, mul_pow, inv_pow,
    ScaledLimits_sqrt_sq hρ]
  field_simp

private lemma ScaledLimits_hk_ge {g : ℝ} (hg : 0 ≤ g) (k : R3) : 1 ≤ hk g k := by
  unfold hk
  rw [Real.one_le_sqrt]
  have : 0 ≤ 4 * g / ‖k‖ ^ 2 := by positivity
  linarith

private lemma ScaledLimits_rk_sq_lt {g : ℝ} (hg : 0 ≤ g) (k : R3) : rk g k ^ 2 < 1 := by
  have h1 := ScaledLimits_hk_ge hg k
  unfold rk
  rw [div_pow, div_lt_one (by positivity)]
  nlinarith

private lemma ScaledLimits_occDensity_nonneg {g : ℝ} (hg : 0 ≤ g) (k : R3) :
    0 ≤ occDensity g k := by
  have h1 := ScaledLimits_hk_ge hg k
  unfold occDensity
  have : 0 < hk g k := by linarith
  positivity

private lemma ScaledLimits_rate_nonneg {a δ : ℝ} (ha : a ≤ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ riemannRate a δ := by
  unfold riemannRate
  split_ifs with h1 h2
  · exact hδ.le
  · have : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv₀ hδ |>.2 hδ1)
    positivity
  · exact absurd (lt_of_le_of_ne ha h2) h1

/-- The Riemann sum on `P_L` against the full integral, for `0 ≤ a ≤ 2`, `b = 4`. -/
private lemma ScaledLimits_riemann {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (F : R3 → ℝ) (ρ L : ℝ), 0 ≤ C → SingDecay a 4 C F → 0 < ρ →
      ρ ≤ 1 → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      |(L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) *
          (∑' n : Idx, (if inPL ρ L n then F ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0))
        - ((2 * π) ^ 3)⁻¹ * ∫ k, F k|
        ≤ K * C * (ρ ^ (1/200 : ℝ) + riemannRate a (2 * π / (L * ρ ^ (1/2 : ℝ)))) := by
  obtain ⟨K₁, hK₁, h₁⟩ := riemann_PL (a := a) (b := 4) ha (by linarith) (by norm_num)
  obtain ⟨K₂, hK₂, h₂⟩ := integral_sub_setIntegral_shell (a := a) (b := 4) ha (by linarith)
    (by norm_num)
  refine ⟨K₁ + 2 * ((2 * π) ^ 3)⁻¹ * K₂, by positivity, ?_⟩
  intro C F ρ L hC hF hρ hρ1 hL
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hε : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hLs : 0 < L * ρ ^ (1/2 : ℝ) := lt_of_lt_of_le (by positivity) hL
  have hδ : 0 < 2 * π / (L * ρ ^ (1/2 : ℝ)) := by positivity
  have hδ1 : 2 * π / (L * ρ ^ (1/2 : ℝ)) ≤ 1 := by
    rw [div_le_one hLs]; exact hL
  have hrate := ScaledLimits_rate_nonneg ha2 hδ hδ1
  have hmeas : MeasurableSet (shellPL ρ) :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hshell : IsShell (epsP ρ) (ENNReal.ofReal (epsP ρ)⁻¹) 0 (shellPL ρ) := by
    refine ⟨fun p h1 h2 => ?_, fun p hp => ⟨hp.1, ENNReal.ofReal_le_ofReal hp.2⟩⟩
    simp only [add_zero] at h1 h2
    exact ⟨h1.le, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg p)).1 h2).le⟩
  obtain ⟨-, hR⟩ := h₁ C F ρ L hC hF hρ hL
  obtain ⟨-, hS⟩ := h₂ C F (epsP ρ) (ENNReal.ofReal (epsP ρ)⁻¹) (shellPL ρ) hC hF hε.le
    (by simpa using hε) hmeas hshell
  have hinv : ((ENNReal.ofReal (epsP ρ)⁻¹)⁻¹).toReal = epsP ρ := by
    rw [← ENNReal.ofReal_inv_of_pos (inv_pos.2 hε), inv_inv, ENNReal.toReal_ofReal hε.le]
  rw [hinv] at hS
  have e1 : epsP ρ ^ (3 - a) ≤ epsP ρ := by
    calc epsP ρ ^ (3 - a) ≤ epsP ρ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
      _ = epsP ρ := Real.rpow_one _
  have e2 : epsP ρ ^ ((4 : ℝ) - 3) = epsP ρ := by
    rw [show (4 : ℝ) - 3 = 1 by norm_num, Real.rpow_one]
  rw [e2] at hS
  set S := (L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) *
    (∑' n : Idx, (if inPL ρ L n then F ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0)) with hSdef
  set c : ℝ := ((2 * π) ^ 3)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set I := ∫ k, F k
  set J := ∫ k in shellPL ρ, F k
  have h3 : |S - c * I| ≤ |S - c * J| + c * |I - J| := by
    calc |S - c * I| = |(S - c * J) + c * (J - I)| := by ring_nf
      _ ≤ |S - c * J| + |c * (J - I)| := abs_add_le _ _
      _ = |S - c * J| + c * |I - J| := by rw [abs_mul, abs_of_nonneg hc0, abs_sub_comm J I]
  have h4 : c * |I - J| ≤ c * (K₂ * C * (2 * epsP ρ)) := by
    refine mul_le_mul_of_nonneg_left (hS.trans ?_) hc0
    have : K₂ * C * (epsP ρ ^ (3 - a) + epsP ρ) ≤ K₂ * C * (2 * epsP ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact this
  have h5 : |S - c * I| ≤ K₁ * C * riemannRate a (2 * π / (L * ρ ^ (1/2 : ℝ))) +
      c * (K₂ * C * (2 * epsP ρ)) := by linarith
  refine h5.trans ?_
  change _ ≤ (K₁ + 2 * c * K₂) * C * (epsP ρ + _)
  have hCe : 0 ≤ C * epsP ρ := by positivity
  nlinarith [mul_nonneg hK₁ hC, mul_nonneg (mul_nonneg hK₁ hC) hrate, mul_nonneg hc0 hK₂,
    mul_nonneg (mul_nonneg hc0 hK₂) hCe, mul_nonneg (mul_nonneg (mul_nonneg hc0 hK₂) hC) hrate]


/-- Prefactor bookkeeping: `f = m F` termwise turns the prefactor `ρ^{-c}` into `ρ^{-3/2}`. -/
private lemma ScaledLimits_scale {ρ L c m : ℝ} (hm : ρ ^ (-c) * m = ρ ^ (-(3 / 2 : ℝ)))
    (f F : Idx → ℝ) (h : ∀ n, f n = m * F n) :
    (L ^ 3)⁻¹ * ρ ^ (-c) * (∑' n, f n) = (L ^ 3)⁻¹ * ρ ^ (-(3 / 2 : ℝ)) * (∑' n, F n) := by
  simp_rw [h]
  rw [tsum_mul_left, ← hm]
  ring

private lemma ScaledLimits_rate_one (δ : ℝ) : riemannRate 1 δ = δ := by
  unfold riemannRate
  norm_num

/-- (5.35)–(5.36) [3.1, sum]. -/
theorem sum_PL_occ {g : ℝ} (hg : 0 < g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ L : ℝ, 0 < ρ → ρ ≤ 1 → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      |(L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) *
          (∑' n : Idx, (if inPL ρ L n then
            (ρ * lamPL g ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL g ρ (mom L n)) ^ 2) else 0))
        - g ^ (3/2 : ℝ) / (3 * π ^ 2)|
        ≤ K * (ρ ^ (1/200 : ℝ) + 2 * π / (L * ρ ^ (1/2 : ℝ))) := by
  obtain ⟨C, hC, hF⟩ := singDecay_occDensity hg
  obtain ⟨K, hK, h⟩ := ScaledLimits_riemann (a := 1) zero_le_one (by norm_num)
  refine ⟨K * C, by positivity, fun ρ L hρ hρ1 hL => ?_⟩
  have h1 := h C (occDensity g) ρ L hC hF hρ hρ1 hL
  rw [ScaledLimits_rate_one] at h1
  have hint := (integral_occDensity hg.le).2
  have hsum := ScaledLimits_scale (ρ := ρ) (L := L) (c := 3/2) (m := 1) (by simp)
    (fun n => if inPL ρ L n then
      (ρ * lamPL g ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL g ρ (mom L n)) ^ 2) else 0)
    (fun n => if inPL ρ L n then occDensity g ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0)
    (fun n => by
      split_ifs
      · rw [rho_mul_lamPL hρ, occDensity_eq hg.le, one_mul]
      · simp)
  rw [hsum, ← hint]
  exact h1

/-- Tails in (5.38) [tail], (5.39) [temp6.35], (5.43) [upt01], (7.21) [temp8.28]. -/
theorem sum_PL_tail {g : ℝ} (hg : 0 < g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ρ L : ℝ, 0 ≤ t → 0 < ρ → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      (L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) *
          ∑' n : Idx, (if inPL ρ L n then
            |ρ * lamPL g ρ (mom L n)| ^ t * ((ρ * lamPL g ρ (mom L n)) ^ 2 /
              (1 - (ρ * lamPL g ρ (mom L n)) ^ 2)) else 0)
        ≤ K * ((1 + t) ^ (-2 : ℝ) + 2 * π / (L * ρ ^ (1/2 : ℝ))) := by
  obtain ⟨C, hC, hF⟩ := singDecay_tailDensity hg
  obtain ⟨K₁, hK₁, h₁⟩ := riemann_PL (a := 1) (b := 4) zero_le_one (by norm_num) (by norm_num)
  obtain ⟨K', hK', h'⟩ := integral_tailDensity_le hg
  refine ⟨K' + K₁ * C, by positivity, fun t ρ L ht hρ hL => ?_⟩
  obtain ⟨-, hR⟩ := h₁ C (tailDensity g t) ρ L hC (hF t ht) hρ hL
  obtain ⟨hI, hv⟩ := h' t ht
  rw [ScaledLimits_rate_one] at hR
  have hnn : ∀ k, 0 ≤ tailDensity g t k := fun k => by
    unfold tailDensity
    exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (ScaledLimits_occDensity_nonneg hg.le k)
  have hle : ∫ k in shellPL ρ, tailDensity g t k ≤ ∫ k, tailDensity g t k :=
    setIntegral_le_integral hI (ae_of_all _ hnn)
  have hsum := ScaledLimits_scale (ρ := ρ) (L := L) (c := 3/2) (m := 1) (by simp)
    (fun n => if inPL ρ L n then
      |ρ * lamPL g ρ (mom L n)| ^ t * ((ρ * lamPL g ρ (mom L n)) ^ 2 /
        (1 - (ρ * lamPL g ρ (mom L n)) ^ 2)) else 0)
    (fun n => if inPL ρ L n then tailDensity g t ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0)
    (fun n => by
      split_ifs
      · rw [rho_mul_lamPL hρ, occDensity_eq hg.le, one_mul]
        rfl
      · simp)
  rw [hsum]
  have hδ : 0 ≤ 2 * π / (L * ρ ^ (1/2 : ℝ)) := by
    have hLs : 0 < L * ρ ^ (1/2 : ℝ) := lt_of_lt_of_le (by positivity) hL
    positivity
  have hp : 0 ≤ (1 + t) ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hc : 0 ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  have h2 := (abs_le.1 hR).2
  have h3 := mul_le_mul_of_nonneg_left hle hc
  have h4 : K₁ * C * (2 * π / (L * ρ ^ (1/2 : ℝ))) ≤
      (K₁ * C) * ((1 + t) ^ (-2 : ℝ) + 2 * π / (L * ρ ^ (1/2 : ℝ))) := by
    nlinarith [mul_nonneg hK₁ hC]
  nlinarith [mul_nonneg hK' hp, mul_nonneg hK' hδ, mul_nonneg (mul_nonneg hK₁ hC) hp,
    mul_nonneg (mul_nonneg hK₁ hC) hδ]


/-- (6.3) [boundspsiu2PLtotal]: the `P_L` kinetic sum. -/
theorem sum_PL_kin {g : ℝ} (hg : 0 < g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ L : ℝ, 0 < ρ → ρ ≤ 1 → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      |(L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) *
          (∑' n : Idx, (if inPL ρ L n then ‖mom L n‖ ^ 2 *
            ((ρ * lamPL g ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL g ρ (mom L n)) ^ 2)
              - (ρ * g / ‖mom L n‖ ^ 2) ^ 2) else 0))
        + 8 * g ^ (5/2 : ℝ) / (5 * π ^ 2)|
        ≤ K * (ρ ^ (1/200 : ℝ) + riemannRate 2 (2 * π / (L * ρ ^ (1/2 : ℝ)))) := by
  obtain ⟨C, hC, hF⟩ := singDecay_kinDensity hg
  obtain ⟨K, hK, h⟩ := ScaledLimits_riemann (a := 2) (by norm_num) le_rfl
  refine ⟨K * C, by positivity, fun ρ L hρ hρ1 hL => ?_⟩
  have h1 := h C (kinDensity g) ρ L hC hF hρ hρ1 hL
  have hint := (integral_kinDensity hg.le).2
  have hsum := ScaledLimits_scale (ρ := ρ) (L := L) (c := 5/2) (m := ρ)
    (by
      have := Real.rpow_add hρ (-(5/2 : ℝ)) 1
      rw [Real.rpow_one] at this
      rw [← this]
      norm_num)
    (fun n => if inPL ρ L n then ‖mom L n‖ ^ 2 *
      ((ρ * lamPL g ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL g ρ (mom L n)) ^ 2)
        - (ρ * g / ‖mom L n‖ ^ 2) ^ 2) else 0)
    (fun n => if inPL ρ L n then kinDensity g ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0)
    (fun n => by
      split_ifs
      · have e1 := ScaledLimits_norm_sq hρ (mom L n)
        have e2 : ρ * g / ‖mom L n‖ ^ 2 = g / ‖(ρ ^ (1/2 : ℝ))⁻¹ • mom L n‖ ^ 2 := by
          rw [e1, mul_div_mul_left _ _ hρ.ne']
        rw [rho_mul_lamPL hρ, e2, e1, ← kinDensity_eq hg.le]
        ring
      · simp)
  rw [hint, sub_neg_eq_add] at h1
  rw [hsum]
  exact h1


/-- The `P_L` potential sum in the proof of (7.8) [u-uPL] and of (7.67) [temp8.75]. -/
theorem sum_PL_pot {g : ℝ} (hg : 0 < g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ L : ℝ, 0 < ρ → ρ ≤ 1 → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      |(L ^ 3)⁻¹ * ρ ^ (-(1/2 : ℝ)) *
          (∑' n : Idx, (if inPL ρ L n then
            lamPL g ρ (mom L n) + g / ‖mom L n‖ ^ 2
              + lamPL g ρ (mom L n) ^ 3 * ρ ^ 2 / (1 - ρ ^ 2 * lamPL g ρ (mom L n) ^ 2)
            else 0))
        - g ^ (3/2 : ℝ) / π ^ 2|
        ≤ K * (ρ ^ (1/200 : ℝ) + riemannRate 2 (2 * π / (L * ρ ^ (1/2 : ℝ)))) := by
  obtain ⟨C, hC, hF⟩ := singDecay_potDensity hg
  obtain ⟨K, hK, h⟩ := ScaledLimits_riemann (a := 2) (by norm_num) le_rfl
  refine ⟨K * C, by positivity, fun ρ L hρ hρ1 hL => ?_⟩
  have h1 := h C (potDensity g) ρ L hC hF hρ hρ1 hL
  have hint := (integral_potDensity hg.le).2
  have hsum := ScaledLimits_scale (ρ := ρ) (L := L) (c := 1/2) (m := ρ⁻¹)
    (by
      have := Real.rpow_add hρ (-(1/2 : ℝ)) (-1)
      rw [Real.rpow_neg_one] at this
      rw [← this]
      norm_num)
    (fun n => if inPL ρ L n then
      lamPL g ρ (mom L n) + g / ‖mom L n‖ ^ 2
        + lamPL g ρ (mom L n) ^ 3 * ρ ^ 2 / (1 - ρ ^ 2 * lamPL g ρ (mom L n) ^ 2)
      else 0)
    (fun n => if inPL ρ L n then potDensity g ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0)
    (fun n => by
      split_ifs
      · set k : R3 := (ρ ^ (1/2 : ℝ))⁻¹ • mom L n with hk
        have e1 : ‖mom L n‖ ^ 2 = ρ * ‖k‖ ^ 2 := ScaledLimits_norm_sq hρ (mom L n)
        have hl : lamPL g ρ (mom L n) = ρ⁻¹ * rk g k := by
          rw [hk, ← rho_mul_lamPL hρ]
          field_simp
        have hr : 1 - rk g k ^ 2 ≠ 0 := (sub_pos.2 (ScaledLimits_rk_sq_lt hg.le k)).ne'
        have e3 : g / (ρ * ‖k‖ ^ 2) = ρ⁻¹ * (g / ‖k‖ ^ 2) := by ring
        have e4 : 1 - ρ ^ 2 * (ρ⁻¹ * rk g k) ^ 2 = 1 - rk g k ^ 2 := by
          field_simp
        rw [← potDensity_eq hg.le, hl, e1, e3, e4]
        field_simp
        ring
      · simp)
  rw [hint] at h1
  rw [hsum]
  exact h1


/-- The `P_I` sum in the proof of (5.29) [temp4.17]. -/
theorem sum_PI_occ {g : ℝ} (hg : 0 < g) :
    ∃ K ρ₁ : ℝ, 0 ≤ K ∧ 0 < ρ₁ ∧ ∀ (gp : R3 → ℝ) (ρ L : ℝ), (∀ p, |gp p| ≤ g) →
      0 < ρ → ρ ≤ ρ₁ → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      (L ^ 3)⁻¹ * ∑' n : Idx, (if inPI ρ L n then
          (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2 /
            (1 - (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2) else 0)
        ≤ K * ρ ^ (3/2 + 1/200 : ℝ) := by
  obtain ⟨K₀, hK₀, h₀⟩ := sum_norm_rpow_gt (s := 4) (by norm_num)
  refine ⟨2 * g ^ 2 * K₀, min 1 (((2 * g)⁻¹) ^ 100), by positivity,
    lt_min one_pos (by positivity), ?_⟩
  intro gp ρ L hgp hρ hρ₁ hL
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hε : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hρ1 : ρ ≤ 1 := hρ₁.trans (min_le_left _ _)
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hε200 : (epsP ρ ^ 2) ^ 100 = ρ := by
    unfold epsP
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have hε2 : g * epsP ρ ^ 2 ≤ 1 / 2 := by
    have h1 : epsP ρ ^ 2 ≤ (2 * g)⁻¹ :=
      le_of_pow_le_pow_left₀ (n := 100) (by norm_num) (by positivity)
        (by rw [hε200]; exact hρ₁.trans (min_le_right _ _))
    calc g * epsP ρ ^ 2 ≤ g * (2 * g)⁻¹ := mul_le_mul_of_nonneg_left h1 hg.le
      _ = 1 / 2 := by field_simp
  set R : ℝ := (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) with hRdef
  have hR : 0 < R := by positivity
  have hLpos : 0 < L := by
    have : 0 < L * ρ ^ (1/2 : ℝ) := lt_of_lt_of_le (by positivity) hL
    exact pos_of_mul_pos_left this hs.le
  have hsR : ρ ^ (1/2 : ℝ) ≤ R := by
    have : 1 ≤ (epsP ρ)⁻¹ := (one_le_inv₀ hε).2 hε1
    nlinarith
  have hLR : 2 * π ≤ L * R := hL.trans (mul_le_mul_of_nonneg_left hsR hLpos.le)
  obtain ⟨hsm, hle⟩ := h₀ L R hR hLR
  have hterm : ∀ n : Idx,
      0 ≤ (if inPI ρ L n then
          (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2 /
            (1 - (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2) else 0) ∧
      (if inPI ρ L n then
          (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2 /
            (1 - (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2) else 0) ≤
        2 * g ^ 2 * ρ ^ 2 * (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-(4 : ℝ)) else 0) := by
    intro n
    have hM : 0 ≤ 2 * g ^ 2 * ρ ^ 2 *
        (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-(4 : ℝ)) else 0) := by
      split_ifs
      · exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
      · simp
    by_cases hn : inPI ρ L n
    · have hx : R < ‖mom L n‖ := hn.1
      have hx0 : 0 < ‖mom L n‖ := hR.trans hx
      simp only [hn, hx, ↓reduceIte]
      set x := ‖mom L n‖ with hxdef
      have hρx : ρ ≤ epsP ρ ^ 2 * x ^ 2 := by
        have h1 : ρ ^ (1/2 : ℝ) < epsP ρ * x := by
          have := mul_lt_mul_of_pos_left hx hε
          rwa [hRdef, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at this
        have h2 := ScaledLimits_sqrt_sq hρ
        nlinarith [Real.rpow_pos_of_pos hρ (1/2 : ℝ)]
      have hx2 : 0 < x ^ 2 := by positivity
      set y := ρ * gp (mom L n) / x ^ 2 with hy
      have hy1 : y ^ 2 ≤ g ^ 2 * ρ ^ 2 * (x ^ 4)⁻¹ := by
        have e : y ^ 2 = (ρ * gp (mom L n)) ^ 2 * (x ^ 4)⁻¹ := by
          rw [hy, div_pow, ← pow_mul, div_eq_mul_inv]
        rw [e]
        have h3 : (gp (mom L n)) ^ 2 ≤ g ^ 2 := sq_le_sq' (abs_le.1 (hgp _)).1 (abs_le.1 (hgp _)).2
        have : 0 ≤ (x ^ 4)⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h3 (mul_nonneg (sq_nonneg ρ) this)]
      have hy2 : y ^ 2 ≤ 1 / 4 := by
        have h4 : |y| ≤ g * epsP ρ ^ 2 := by
          rw [hy, abs_div, abs_mul, abs_of_pos hρ, abs_of_pos hx2, div_le_iff₀ hx2]
          have := mul_le_mul_of_nonneg_left (hgp (mom L n)) hρ.le
          nlinarith [abs_nonneg (gp (mom L n))]
        have h5 : |y| ≤ 1 / 2 := h4.trans hε2
        have h6 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        nlinarith [abs_nonneg y]
      have hy3 : y ^ 2 / (1 - y ^ 2) ≤ 2 * y ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [sq_nonneg y]
      have e4 : x ^ (-(4 : ℝ)) = (x ^ 4)⁻¹ := by
        rw [Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [e4]
      refine ⟨div_nonneg (sq_nonneg _) (by linarith), ?_⟩
      calc y ^ 2 / (1 - y ^ 2) ≤ 2 * y ^ 2 := hy3
        _ ≤ 2 * (g ^ 2 * ρ ^ 2 * (x ^ 4)⁻¹) := by linarith
        _ = 2 * g ^ 2 * ρ ^ 2 * (x ^ 4)⁻¹ := by ring
    · simp only [hn, ↓reduceIte]
      exact ⟨le_rfl, hM⟩
  have hsumM : Summable (fun n : Idx => 2 * g ^ 2 * ρ ^ 2 *
      (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-(4 : ℝ)) else 0)) := hsm.mul_left _
  have hsumf := Summable.of_nonneg_of_le (fun n => (hterm n).1) (fun n => (hterm n).2) hsumM
  have h1 := hsumf.tsum_le_tsum (fun n => (hterm n).2) hsumM
  rw [tsum_mul_left] at h1
  have hRinv : R ^ (3 - 4 : ℝ) = epsP ρ * (ρ ^ (1/2 : ℝ))⁻¹ := by
    rw [show (3 - 4 : ℝ) = -1 by norm_num, Real.rpow_neg_one, hRdef, mul_inv, inv_inv]
  have hexp : ρ ^ 2 * (epsP ρ * (ρ ^ (1/2 : ℝ))⁻¹) = ρ ^ (3/2 + 1/200 : ℝ) := by
    rw [show (3/2 + 1/200 : ℝ) = 2 + 1/200 + -(1/2) by norm_num, Real.rpow_add hρ,
      Real.rpow_add hρ, Real.rpow_neg hρ.le, Real.rpow_two]
    unfold epsP
    ring
  rw [hRinv] at hle
  calc (L ^ 3)⁻¹ * ∑' n : Idx, (if inPI ρ L n then
          (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2 /
            (1 - (ρ * gp (mom L n) / ‖mom L n‖ ^ 2) ^ 2) else 0)
      ≤ (L ^ 3)⁻¹ * (2 * g ^ 2 * ρ ^ 2 *
          ∑' n : Idx, (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-(4 : ℝ)) else 0)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * g ^ 2 * ρ ^ 2 * ((L ^ 3)⁻¹ *
          ∑' n : Idx, (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-(4 : ℝ)) else 0)) := by ring
    _ ≤ 2 * g ^ 2 * ρ ^ 2 * (K₀ * (epsP ρ * (ρ ^ (1/2 : ℝ))⁻¹)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * g ^ 2 * K₀ * (ρ ^ 2 * (epsP ρ * (ρ ^ (1/2 : ℝ))⁻¹)) := by ring
    _ = 2 * g ^ 2 * K₀ * ρ ^ (3/2 + 1/200 : ℝ) := by rw [hexp]


/-- A function on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma ScaledLimits_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
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


/-- Termwise bound for the replacement `ρ₀ gp → ρ g` on one lattice point. -/
private lemma ScaledLimits_kin_replace_term {g C' κ ρ σ x p : ℝ} (hg : 0 < g) (hκ : 0 ≤ κ)
    (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ) (hx : 0 < x) (hp : |p| ≤ g)
    (hpd : |p - g| ≤ C' * x) :
    |x ^ 2 * ((ρ * g / x ^ 2) ^ 2 - ((ρ - κ * σ) * (p / x ^ 2)) ^ 2)| ≤
      g * (2 + κ) * ρ ^ 2 * C' * x⁻¹ + g * (2 + κ) * κ * g * (ρ * σ) * (x ^ 2)⁻¹ := by
  have hC' : 0 ≤ C' := by
    have := (abs_nonneg (p - g)).trans hpd
    by_contra h
    push Not at h
    nlinarith
  have hx2 : 0 < x ^ 2 := by positivity
  have e : x ^ 2 * ((ρ * g / x ^ 2) ^ 2 - ((ρ - κ * σ) * (p / x ^ 2)) ^ 2) =
      ((ρ * g) ^ 2 - ((ρ - κ * σ) * p) ^ 2) / x ^ 2 := by
    field_simp
  rw [e, abs_div, abs_of_pos hx2, div_le_iff₀ hx2]
  have h1 : |ρ * g - (ρ - κ * σ) * p| ≤ ρ * C' * x + κ * σ * g := by
    have e1 : ρ * g - (ρ - κ * σ) * p = ρ * (g - p) + κ * σ * p := by ring
    rw [e1]
    calc |ρ * (g - p) + κ * σ * p| ≤ |ρ * (g - p)| + |κ * σ * p| := abs_add_le _ _
      _ = ρ * |p - g| + κ * σ * |p| := by
          rw [abs_mul, abs_of_pos hρ, abs_sub_comm, abs_mul, abs_of_nonneg (mul_nonneg hκ hσ)]
      _ ≤ ρ * (C' * x) + κ * σ * g := by
          gcongr
      _ = ρ * C' * x + κ * σ * g := by ring
  have h2 : |ρ * g + (ρ - κ * σ) * p| ≤ g * ρ * (2 + κ) := by
    have h3 : |ρ - κ * σ| ≤ ρ * (1 + κ) := by
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg hκ hσ, mul_le_mul_of_nonneg_left hσρ hκ]
    calc |ρ * g + (ρ - κ * σ) * p| ≤ |ρ * g| + |(ρ - κ * σ) * p| := abs_add_le _ _
      _ = ρ * g + |ρ - κ * σ| * |p| := by rw [abs_mul, abs_mul, abs_of_pos hρ, abs_of_pos hg]
      _ ≤ ρ * g + ρ * (1 + κ) * g := by gcongr
      _ = g * ρ * (2 + κ) := by ring
  have h4 : |(ρ * g) ^ 2 - ((ρ - κ * σ) * p) ^ 2| ≤
      (ρ * C' * x + κ * σ * g) * (g * ρ * (2 + κ)) := by
    have : (ρ * g) ^ 2 - ((ρ - κ * σ) * p) ^ 2 =
        (ρ * g - (ρ - κ * σ) * p) * (ρ * g + (ρ - κ * σ) * p) := by ring
    rw [this, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  refine h4.trans (le_of_eq ?_)
  field_simp


/-- The replacement `ρ₀w_u → ρg₀|u|^{-2}` on `P_L` in the proof of (6.3). -/
theorem sum_PL_kin_replace {g C : ℝ} (hg : 0 < g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (gp : R3 → ℝ) (ρ L : ℝ), (∀ p, |gp p| ≤ g) →
      (∀ p, |gp p - g| ≤ C * ‖p‖) → 0 < ρ → ρ ≤ 1 → 2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      |(L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) *
          ∑' n : Idx, (if inPL ρ L n then ‖mom L n‖ ^ 2 *
            ((ρ * g / ‖mom L n‖ ^ 2) ^ 2 - (rho0 g ρ * (gp (mom L n) / ‖mom L n‖ ^ 2)) ^ 2)
            else 0)|
        ≤ K * ρ ^ (1/2 - 2/200 : ℝ) := by
  obtain ⟨K₁, hK₁, h₁⟩ := sum_norm_rpow_le (s := 1) (by norm_num)
  obtain ⟨K₂, hK₂, h₂⟩ := sum_norm_rpow_le (s := 2) (by norm_num)
  set κ : ℝ := (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨g * (2 + κ) * |C| * K₁ + g * (2 + κ) * κ * g * K₂, by positivity, ?_⟩
  intro gp ρ L hgp hgd hρ hρ1 hL
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hε : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  set R : ℝ := (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) with hRdef
  have hR : 0 < R := by positivity
  have hLpos : 0 < L := by
    have : 0 < L * ρ ^ (1/2 : ℝ) := lt_of_lt_of_le (by positivity) hL
    exact pos_of_mul_pos_left this hs.le
  have hsR : ρ ^ (1/2 : ℝ) ≤ R := by
    have : 1 ≤ (epsP ρ)⁻¹ := (one_le_inv₀ hε).2 hε1
    nlinarith
  have hLR : 2 * π ≤ L * R := hL.trans (mul_le_mul_of_nonneg_left hsR hLpos.le)
  have hσ0 : 0 < ρ ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hσρ : ρ ^ (3/2 : ℝ) ≤ ρ := by
    calc ρ ^ (3/2 : ℝ) ≤ ρ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
      _ = ρ := Real.rpow_one ρ
  set A : ℝ := g * (2 + κ) * ρ ^ 2 * |C| with hA
  set B : ℝ := g * (2 + κ) * κ * g * (ρ * ρ ^ (3/2 : ℝ)) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set m1 : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(1 : ℝ)) else 0
    with hm1
  set m2 : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(2 : ℝ)) else 0
    with hm2
  have hm1s : Summable m1 := ScaledLimits_summable_ball hLpos (R := R) m1 (fun n hn => by
    by_contra h
    exact hn (by simp [hm1, h]))
  have hm2s : Summable m2 := ScaledLimits_summable_ball hLpos (R := R) m2 (fun n hn => by
    by_contra h
    exact hn (by simp [hm2, h]))
  have hm1n : ∀ n, 0 ≤ m1 n := fun n => by
    simp only [hm1]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hm2n : ∀ n, 0 ≤ m2 n := fun n => by
    simp only [hm2]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hmsum : Summable (fun n => A * m1 n + B * m2 n) := (hm1s.mul_left A).add (hm2s.mul_left B)
  have hρ0 : rho0 g ρ = ρ - κ * ρ ^ (3/2 : ℝ) := by
    unfold rho0
    ring
  set f : Idx → ℝ := fun n => if inPL ρ L n then ‖mom L n‖ ^ 2 *
            ((ρ * g / ‖mom L n‖ ^ 2) ^ 2 - (rho0 g ρ * (gp (mom L n) / ‖mom L n‖ ^ 2)) ^ 2)
            else 0 with hfdef
  have hbd : ∀ n : Idx, |f n| ≤ A * m1 n + B * m2 n := by
    intro n
    by_cases hn : inPL ρ L n
    · have hx0 : 0 < ‖mom L n‖ := lt_of_lt_of_le (by positivity) hn.1
      have hn0 : n ≠ 0 := by
        rintro rfl
        have h0 : mom L 0 = 0 := by
          ext i
          simp [mom]
        rw [h0, norm_zero] at hx0
        exact lt_irrefl _ hx0
      have hxR : ‖mom L n‖ ≤ R := hn.2
      have hfn : f n = ‖mom L n‖ ^ 2 *
            ((ρ * g / ‖mom L n‖ ^ 2) ^ 2 - ((ρ - κ * ρ ^ (3/2 : ℝ)) *
              (gp (mom L n) / ‖mom L n‖ ^ 2)) ^ 2) := by
        rw [hfdef]
        simp only [hn, ↓reduceIte, hρ0]
      rw [hfn]
      have hpd : |gp (mom L n) - g| ≤ |C| * ‖mom L n‖ :=
        (hgd _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
      have := ScaledLimits_kin_replace_term (g := g) (C' := |C|) (κ := κ) (ρ := ρ)
        (σ := ρ ^ (3/2 : ℝ)) hg hκ0 hρ hσ0.le hσρ hx0 (hgp _) hpd
      refine this.trans (le_of_eq ?_)
      have e1 : ‖mom L n‖ ^ (-(1 : ℝ)) = ‖mom L n‖⁻¹ := Real.rpow_neg_one _
      have e2 : ‖mom L n‖ ^ (-(2 : ℝ)) = (‖mom L n‖ ^ 2)⁻¹ := by
        rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hc : n ≠ 0 ∧ ‖mom L n‖ ≤ R := ⟨hn0, hxR⟩
      simp only [hm1, hm2, eq_true hc, ↓reduceIte, e1, e2]
      ring
    · have hf0 : f n = 0 := by
        rw [hfdef]
        simp only [hn, ↓reduceIte]
      rw [hf0, abs_zero]
      exact add_nonneg (mul_nonneg hA0 (hm1n n)) (mul_nonneg hB0 (hm2n n))
  have hsum : |∑' n : Idx, f n| ≤ ∑' n : Idx, (A * m1 n + B * m2 n) := by
    by_cases hsf : Summable f
    · have h1 : |∑' n : Idx, f n| ≤ ∑' n : Idx, |f n| := by
        have := norm_tsum_le_tsum_norm (f := f) hsf.norm
        simpa only [Real.norm_eq_abs] using this
      exact h1.trans (hsf.abs.tsum_le_tsum hbd hmsum)
    · rw [tsum_eq_zero_of_not_summable hsf, abs_zero]
      exact tsum_nonneg fun n => add_nonneg (mul_nonneg hA0 (hm1n n)) (mul_nonneg hB0 (hm2n n))
  have hT1 := h₁ L R hR hLR
  have hT2 := h₂ L R hR hLR
  have hRe : R = ρ ^ (1/2 - 1/200 : ℝ) := by
    rw [hRdef, epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
    congr 1
    ring
  have hR2 : R ^ (3 - 1 : ℝ) = ρ ^ (1 - 1/100 : ℝ) := by
    rw [hRe, ← Real.rpow_mul hρ.le]
    congr 1
    norm_num
  have hE1 : ρ ^ (-(5/2 : ℝ)) * (ρ ^ 2 * R ^ (3 - 1 : ℝ)) = ρ ^ (1/2 - 2/200 : ℝ) := by
    rw [hR2, ← Real.rpow_two, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    congr 1
    norm_num
  have hE2 : ρ ^ (-(5/2 : ℝ)) * ((ρ * ρ ^ (3/2 : ℝ)) * R ^ (3 - 2 : ℝ)) ≤
      ρ ^ (1/2 - 2/200 : ℝ) := by
    have e5 : ρ * ρ ^ (3/2 : ℝ) = ρ ^ (5/2 : ℝ) := by
      rw [show (5/2 : ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hρ, Real.rpow_one]
    have e : ρ ^ (-(5/2 : ℝ)) * ((ρ * ρ ^ (3/2 : ℝ)) * R ^ (3 - 2 : ℝ)) =
        ρ ^ (1/2 - 1/200 : ℝ) := by
      rw [e5, hRe, show (3 - 2 : ℝ) = 1 by norm_num, Real.rpow_one, ← Real.rpow_add hρ,
        ← Real.rpow_add hρ]
      congr 1
      norm_num
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hpre : 0 ≤ (L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) := by positivity
  rw [abs_mul, abs_of_nonneg hpre]
  have htm : ∑' n : Idx, (A * m1 n + B * m2 n) =
      A * (∑' n, m1 n) + B * (∑' n, m2 n) := by
    rw [(hm1s.mul_left A).tsum_add (hm2s.mul_left B), tsum_mul_left, tsum_mul_left]
  calc (L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) * |∑' n : Idx, f n|
      ≤ (L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) * (A * (∑' n, m1 n) + B * (∑' n, m2 n)) :=
        mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq htm)) hpre
    _ = ρ ^ (-(5/2 : ℝ)) * (A * ((L ^ 3)⁻¹ * ∑' n, m1 n) + B * ((L ^ 3)⁻¹ * ∑' n, m2 n)) := by
        ring
    _ ≤ ρ ^ (-(5/2 : ℝ)) * (A * (K₁ * R ^ (3 - 1 : ℝ)) + B * (K₂ * R ^ (3 - 2 : ℝ))) := by
        gcongr
    _ = (g * (2 + κ) * |C| * K₁) * (ρ ^ (-(5/2 : ℝ)) * (ρ ^ 2 * R ^ (3 - 1 : ℝ))) +
          (g * (2 + κ) * κ * g * K₂) *
            (ρ ^ (-(5/2 : ℝ)) * ((ρ * ρ ^ (3/2 : ℝ)) * R ^ (3 - 2 : ℝ))) := by
        rw [hA, hB]; ring
    _ ≤ (g * (2 + κ) * |C| * K₁) * ρ ^ (1/2 - 2/200 : ℝ) +
          (g * (2 + κ) * κ * g * K₂) * ρ ^ (1/2 - 2/200 : ℝ) := by
        rw [hE1]
        gcongr
    _ = (g * (2 + κ) * |C| * K₁ + g * (2 + κ) * κ * g * K₂) * ρ ^ (1/2 - 2/200 : ℝ) := by ring


end LHYUpper
