import LHYUpper.Scattering.WMomentum
import LHYUpper.TrialState.Regions

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # The function `λ_k` and its bounds

Closed form and bounds for `λ_k` of (3.15) [lambda]: `λ_k = -w_k` off `P_L`, `|λ_k| ≤ g₀/|k|²` on
`P_L ∪ P_I ∪ P_H` and `|ρλ_k| ≤ 1 - cε` for small `ρ` ((5.9) [ublambda]), the negativity `-ρ⁻¹ < λ_k
< 0` and the bound `λ_k ≤ -(g₀/2)ε²ρ⁻¹` on `P_L` ((5.10) [lublambdaPL0]), the bound `|λ_k| ≤ g₀/ε²`
on `P_H` ((5.11) [ublambdaPH0]), and the Lipschitz-type bound `|λ_n - λ_m| ≤ Cε^{-3}|p_n + p_m|`
used in §8 and the proof of Lemma 10.2 [101]. -/

section Helpers

private lemma Lambda_eps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < epsP ρ := by
  unfold epsP
  positivity

private lemma Lambda_eps_le_one {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) : epsP ρ ≤ 1 :=
  Real.rpow_le_one hρ.le h1 (by norm_num)

private lemma Lambda_sqrt_sq {ρ : ℝ} (hρ : 0 < ρ) : (ρ ^ (1/2 : ℝ)) ^ 2 = ρ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

private lemma Lambda_eps_sq {ρ : ℝ} (hρ : 0 < ρ) : epsP ρ ^ 2 = ρ ^ (1/100 : ℝ) := by
  unfold epsP
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

private lemma Lambda_rho_le_eps_sq_sq {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) :
    ρ ≤ epsP ρ ^ 2 * epsP ρ ^ 2 := by
  have : epsP ρ ^ 2 * epsP ρ ^ 2 = ρ ^ (1/50 : ℝ) := by
    rw [Lambda_eps_sq hρ, ← Real.rpow_add hρ]
    norm_num
  rw [this]
  calc ρ = ρ ^ (1 : ℝ) := (Real.rpow_one ρ).symm
    _ ≤ ρ ^ (1/50 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hρ h1 (by norm_num)

/-- For `ρ < 1`, `√ρ < ε²`, so a momentum with `|k| ≥ ε` is not in `P_L`. -/
private lemma Lambda_not_PL_of_ge {ρ L : ℝ} (hρ : 0 < ρ) (h1 : ρ < 1) {n : Idx}
    (h : epsP ρ ≤ ‖mom L n‖) : ¬ inPL ρ L n := by
  intro hL
  have he := Lambda_eps_pos hρ
  have hs : 0 < ρ ^ (1/2 : ℝ) := by positivity
  have h2 : ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := hL.2
  have h3 : epsP ρ * epsP ρ ≤ ρ ^ (1/2 : ℝ) := by
    calc epsP ρ * epsP ρ ≤ epsP ρ * ‖mom L n‖ := mul_le_mul_of_nonneg_left h he.le
      _ ≤ epsP ρ * ((epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ)) := mul_le_mul_of_nonneg_left h2 he.le
      _ = ρ ^ (1/2 : ℝ) := by field_simp
  have h4 : epsP ρ * epsP ρ = ρ ^ (1/100 : ℝ) := by
    unfold epsP
    rw [← Real.rpow_add hρ]
    norm_num
  rw [h4] at h3
  have h5 : ρ ^ (1/2 : ℝ) < ρ ^ (1/100 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_gt hρ h1 (by norm_num)
  linarith

/-- On `P_L`: `|k| > 0`, `ε²ρ ≤ |k|²` and `ε²|k|² ≤ ρ`. -/
private lemma Lambda_PL_sq_bounds {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPL ρ L n) :
    0 < ‖mom L n‖ ∧ epsP ρ ^ 2 * ρ ≤ ‖mom L n‖ ^ 2 ∧ epsP ρ ^ 2 * ‖mom L n‖ ^ 2 ≤ ρ := by
  have he := Lambda_eps_pos hρ
  have hs : 0 < ρ ^ (1/2 : ℝ) := by positivity
  have hss := Lambda_sqrt_sq hρ
  have h1 : epsP ρ * ρ ^ (1/2 : ℝ) ≤ ‖mom L n‖ := h.1
  have h2 : ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := h.2
  have h3 : epsP ρ * ‖mom L n‖ ≤ ρ ^ (1/2 : ℝ) := by
    calc epsP ρ * ‖mom L n‖ ≤ epsP ρ * ((epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 he.le
      _ = ρ ^ (1/2 : ℝ) := by field_simp
  have hk : 0 < ‖mom L n‖ := lt_of_lt_of_le (mul_pos he hs) h1
  refine ⟨hk, ?_, ?_⟩
  · have := pow_le_pow_left₀ (mul_pos he hs).le h1 2
    rw [mul_pow, hss] at this
    exact this
  · have := pow_le_pow_left₀ (mul_pos he hk).le h3 2
    rw [mul_pow, hss] at this
    exact this

/-- The closed form of `λ_k` on `P_L` with `s = √(1 + 4ρg₀/|k|²)`. -/
private lemma Lambda_PL_form {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx}
    (h : inPL ρ L n) :
    ∃ s : ℝ, 1 < s ∧ ‖mom L n‖ ^ 2 * (s ^ 2 - 1) = 4 * ρ * g0 V w ∧
      lam V w ρ L n = (1 - s) / (1 + s) / ρ := by
  obtain ⟨hk, -, -⟩ := Lambda_PL_sq_bounds hρ h
  have hk2 : 0 < ‖mom L n‖ ^ 2 := by positivity
  have hx : 0 < 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 := by positivity
  refine ⟨Real.sqrt (1 + 4 * ρ * g0 V w / ‖mom L n‖ ^ 2), ?_, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]
    linarith
  · rw [Real.sq_sqrt (by linarith)]
    field_simp
    ring
  · unfold lam
    simp only [h, ↓reduceIte]

/-- `ε → 0` as `ρ → 0⁺`. -/
private lemma Lambda_eps_tendsto : Tendsto epsP (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const (0 : ℝ) (1/200 : ℝ) (Or.inr (by norm_num))).tendsto
  rw [Real.zero_rpow (by norm_num)] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- For small `ρ > 0`: `ρ < 1` and `ε ≤ δ`. -/
private lemma Lambda_eventually_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ < 1 ∧ epsP ρ ≤ δ := by
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), epsP ρ ≤ δ := Lambda_eps_tendsto.eventually (eventually_le_nhds hδ)
  filter_upwards [h1, h2, h3] with ρ a b c
  exact ⟨a, b, c⟩

end Helpers

section
variable {V w : R3 → ℝ}

/-- Off `P_L`, `λ_k = −w_k`, (3.15) [lambda]. -/
theorem scat_lam_of_not_PL (ρ L : ℝ) (n : Idx) (h : ¬ inPL ρ L n) :
    lam V w ρ L n = -wmom V w (mom L n) := by
  unfold lam wmom
  simp only [h, ↓reduceIte, neg_div]

/-- Off `P_L`, on `P_I ∪ P_H`: `|ρλ_k| ≤ g₀ε²` for `0 < ρ ≤ 1`. -/
private lemma Lambda_rho_abs_off (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) {ρ L : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) {n : Idx}
    (h : inPI ρ L n ∨ inPH ρ L n) : |ρ * lam V w ρ L n| ≤ g0 V w * epsP ρ ^ 2 := by
  have hg := scat_g0_pos hV hw
  have he := Lambda_eps_pos hρ
  have hρe := Lambda_rho_le_eps_sq_sq hρ h1
  have hnot : ¬ inPL ρ L n := by
    rcases h with hI | hH
    · exact fun hL => Regions_PL_PI hL hI
    · exact fun hL => Regions_PL_PH hρ hL hH
  have hs : 0 < ρ ^ (1/2 : ℝ) := by positivity
  have hss := Lambda_sqrt_sq hρ
  have hkey : ρ ≤ epsP ρ ^ 2 * ‖mom L n‖ ^ 2 ∧ 0 < ‖mom L n‖ := by
    rcases h with hI | hH
    · have h2 : (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) < ‖mom L n‖ := hI.1
      have h3 : ρ ^ (1/2 : ℝ) < epsP ρ * ‖mom L n‖ := by
        have := mul_lt_mul_of_pos_left h2 he
        rwa [← mul_assoc, mul_inv_cancel₀ he.ne', one_mul] at this
      have h4 := pow_lt_pow_left₀ h3 hs.le (by norm_num : 2 ≠ 0)
      rw [hss, mul_pow] at h4
      refine ⟨h4.le, ?_⟩
      by_contra hk
      have : ‖mom L n‖ = 0 := le_antisymm (not_lt.1 hk) (norm_nonneg _)
      rw [this] at h3
      linarith [mul_zero (epsP ρ)]
    · have h2 : epsP ρ < ‖mom L n‖ := hH
      have h3 := pow_lt_pow_left₀ h2 he.le (by norm_num : 2 ≠ 0)
      refine ⟨?_, he.trans h2⟩
      have : 0 < epsP ρ ^ 2 := by positivity
      nlinarith
  obtain ⟨hk1, hk⟩ := hkey
  have hk2 : 0 < ‖mom L n‖ ^ 2 := by positivity
  rw [abs_mul, abs_of_pos hρ, scat_lam_of_not_PL ρ L n hnot, abs_neg]
  calc ρ * |wmom V w (mom L n)| ≤ ρ * (g0 V w / ‖mom L n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (scat_wmom_abs_le hV hw _) hρ.le
    _ = ρ * g0 V w / ‖mom L n‖ ^ 2 := by ring
    _ ≤ g0 V w * epsP ρ ^ 2 := by
        rw [div_le_iff₀ hk2]
        nlinarith [mul_le_mul_of_nonneg_left hk1 hg.le]

/-- (5.9) [ublambda]: `|λ_k| ≤ g₀/|k|²` on `P_L ∪ P_I ∪ P_H`. -/
theorem scat_lam_abs_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ ρ, 0 < ρ → ∀ L n, (inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n) →
      |lam V w ρ L n| ≤ g0 V w / ‖mom L n‖ ^ 2 := by
  intro ρ hρ L n _
  by_cases h : inPL ρ L n
  · have hg := scat_g0_pos hV hw
    obtain ⟨s, hs1, hs2, hl⟩ := Lambda_PL_form hg hρ h
    obtain ⟨hk, -, -⟩ := Lambda_PL_sq_bounds hρ h
    have hk2 : 0 < ‖mom L n‖ ^ 2 := by positivity
    have hs0 : 0 < 1 + s := by linarith
    rw [hl, abs_div, abs_div, abs_of_pos hs0, abs_of_pos hρ, abs_of_neg (by linarith : 1 - s < 0),
      div_div, div_le_div_iff₀ (by positivity) hk2]
    have h4 : 4 ≤ (1 + s) ^ 2 := by nlinarith
    have h5 : (s - 1) * (1 + s) * ‖mom L n‖ ^ 2 = 4 * ρ * g0 V w := by
      rw [← hs2]
      ring
    have h6 : 0 < g0 V w * ρ := mul_pos hg hρ
    nlinarith [mul_pos h6 hs0, mul_nonneg hk2.le (by linarith : (0 : ℝ) ≤ s - 1)]
  · rw [scat_lam_of_not_PL ρ L n h, abs_neg]
    exact scat_wmom_abs_le hV hw _

/-- (5.9) [ublambda]: `|ρλ_k| ≤ 1 − cε` for `ρ` small. -/
theorem scat_rho_lam_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ c > 0, ∀ᶠ ρ in 𝓝[>] 0, ∀ L n, (inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n) →
      |ρ * lam V w ρ L n| ≤ 1 - c * epsP ρ := by
  have hg := scat_g0_pos hV hw
  refine ⟨1 / (1 + g0 V w), by positivity, ?_⟩
  filter_upwards [Lambda_eventually_small (δ := 1 / (2 * (1 + g0 V w))) (by positivity)]
    with ρ hρ'
  obtain ⟨hρ, hρ1, hεδ⟩ := hρ'
  intro L n hn
  have he := Lambda_eps_pos hρ
  have he1 := Lambda_eps_le_one hρ hρ1.le
  have hc1 : g0 V w * epsP ρ ≤ 1 / 2 := by
    have h1 : epsP ρ * (2 * (1 + g0 V w)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hεδ
    nlinarith
  have hc2 : 1 / (1 + g0 V w) * epsP ρ ≤ 1 / 2 := by
    have h1 : epsP ρ * (2 * (1 + g0 V w)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hεδ
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hc : g0 V w * epsP ρ ^ 2 ≤ 1 - 1 / (1 + g0 V w) * epsP ρ := by
    nlinarith
  rcases hn with hL | hI | hH
  · obtain ⟨s, hs1, hs2, hl⟩ := Lambda_PL_form hg hρ hL
    obtain ⟨hk, hk1, -⟩ := Lambda_PL_sq_bounds hρ hL
    have hs0 : 0 < 1 + s := by linarith
    have hρl : ρ * lam V w ρ L n = (1 - s) / (1 + s) := by
      rw [hl]
      field_simp
    have hes : epsP ρ * s ≤ 1 + 2 * g0 V w := by
      have h1 : epsP ρ ^ 2 * (s ^ 2 - 1) ≤ 4 * g0 V w := by
        have h2 : epsP ρ ^ 2 * ρ * (s ^ 2 - 1) ≤ ‖mom L n‖ ^ 2 * (s ^ 2 - 1) :=
          mul_le_mul_of_nonneg_right hk1 (by nlinarith)
        rw [hs2] at h2
        have : ρ * (epsP ρ ^ 2 * (s ^ 2 - 1)) ≤ ρ * (4 * g0 V w) := by nlinarith
        exact le_of_mul_le_mul_left this hρ
      have h3 : (epsP ρ * s) ^ 2 ≤ (1 + 2 * g0 V w) ^ 2 := by
        have : epsP ρ ^ 2 ≤ 1 := by nlinarith
        nlinarith
      exact le_of_sq_le_sq h3 (by linarith)
    rw [hρl, abs_div, abs_of_neg (by linarith : 1 - s < 0), abs_of_pos hs0]
    have h1 : 1 - (s - 1) / (1 + s) = 2 / (1 + s) := by
      field_simp
      ring
    have h2 : 1 / (1 + g0 V w) * epsP ρ ≤ 2 / (1 + s) := by
      rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) hs0]
      nlinarith
    have h3 : (s - 1) / (1 + s) = 1 - 2 / (1 + s) := by
      field_simp
      ring
    rw [neg_sub, h3]
    linarith
  · exact (Lambda_rho_abs_off hV hw hρ hρ1.le (Or.inl hI)).trans hc
  · exact (Lambda_rho_abs_off hV hw hρ hρ1.le (Or.inr hH)).trans hc

/-- `−ρ⁻¹ < λ_k < 0` on `P_L`, (5.10). -/
theorem scat_lam_PL (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ ρ, 0 < ρ → ∀ L n, inPL ρ L n → -ρ⁻¹ < lam V w ρ L n ∧ lam V w ρ L n < 0 := by
  intro ρ hρ L n h
  have hg := scat_g0_pos hV hw
  obtain ⟨s, hs1, -, hl⟩ := Lambda_PL_form hg hρ h
  have hs0 : 0 < 1 + s := by linarith
  rw [hl]
  refine ⟨?_, div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) hs0) hρ⟩
  have : (1 - s) / (1 + s) / ρ - -ρ⁻¹ = 2 / (1 + s) / ρ := by
    field_simp
    ring
  have h2 : 0 < 2 / (1 + s) / ρ := by positivity
  linarith

/-- (5.10) [lublambdaPL0]: `λ_k ≤ −(g₀/2)ε²ρ⁻¹` on `P_L` for `ρ` small. -/
theorem scat_lam_PL_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ᶠ ρ in 𝓝[>] 0, ∀ L n, inPL ρ L n →
      lam V w ρ L n ≤ -(g0 V w / 2) * epsP ρ ^ 2 * ρ⁻¹ := by
  have hg := scat_g0_pos hV hw
  filter_upwards [Lambda_eventually_small (δ := 1 / (1 + g0 V w)) (by positivity)] with ρ hρ'
  obtain ⟨hρ, hρ1, hεδ⟩ := hρ'
  intro L n hL
  have he := Lambda_eps_pos hρ
  have ht : g0 V w * epsP ρ ^ 2 ≤ 1 / 2 := by
    have h1 : epsP ρ * (1 + g0 V w) ≤ 1 := (le_div_iff₀ (by positivity)).1 hεδ
    have h2 : (epsP ρ * (1 + g0 V w)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) h1
    nlinarith [sq_nonneg (g0 V w - 1), sq_nonneg (epsP ρ)]
  obtain ⟨s, hs1, hs2, hl⟩ := Lambda_PL_form hg hρ hL
  obtain ⟨hk, -, hk3⟩ := Lambda_PL_sq_bounds hρ hL
  have hs0 : 0 < 1 + s := by linarith
  set t : ℝ := g0 V w * epsP ρ ^ 2 with htdef
  have htpos : 0 < t := by positivity
  have h4 : 4 * t ≤ s ^ 2 - 1 := by
    have h2 : epsP ρ ^ 2 * ‖mom L n‖ ^ 2 * (s ^ 2 - 1) ≤ ρ * (s ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hk3 (by nlinarith)
    have h3 : epsP ρ ^ 2 * (4 * ρ * g0 V w) ≤ ρ * (s ^ 2 - 1) := by
      rw [← hs2]
      nlinarith
    have : ρ * (4 * t) ≤ ρ * (s ^ 2 - 1) := by
      rw [htdef]
      nlinarith
    exact le_of_mul_le_mul_left this hρ
  have h5 : 2 + t ≤ s * (2 - t) := by
    by_contra hcon
    rw [not_le] at hcon
    have h6 : 0 ≤ s * (2 - t) := by nlinarith
    have h7 := pow_lt_pow_left₀ hcon h6 (by norm_num : 2 ≠ 0)
    nlinarith [mul_pos htpos htpos, mul_pos (mul_pos htpos htpos) htpos]
  have h8 : (1 - s) / (1 + s) ≤ -(t / 2) := by
    rw [div_le_iff₀ hs0]
    nlinarith
  rw [hl]
  calc (1 - s) / (1 + s) / ρ ≤ -(t / 2) / ρ := div_le_div_of_nonneg_right h8 hρ.le
    _ = -(g0 V w / 2) * epsP ρ ^ 2 * ρ⁻¹ := by
        rw [htdef]
        field_simp

/-- (5.11) [ublambdaPH0]: `|λ_k| ≤ g₀/ε²` on `P_H`. -/
theorem scat_lam_PH (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ ρ, 0 < ρ → ∀ L n, inPH ρ L n → |lam V w ρ L n| ≤ g0 V w / epsP ρ ^ 2 := by
  intro ρ hρ L n h
  have hg := scat_g0_pos hV hw
  have he := Lambda_eps_pos hρ
  have hnot : ¬ inPL ρ L n := fun hL => Regions_PL_PH hρ hL h
  rw [scat_lam_of_not_PL ρ L n hnot, abs_neg]
  refine (scat_wmom_abs_le hV hw _).trans ?_
  have h1 : epsP ρ < ‖mom L n‖ := h
  exact div_le_div_of_nonneg_left hg.le (by positivity) (pow_le_pow_left₀ he.le h1.le 2)

/-- `|λ_n − λ_m| ≤ Cε^{-3}|p_n + p_m|` for `p_n + p_m` small (§8 and the proof of Lemma 10.2 [101]). -/
theorem scat_lam_sub_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C, ∀ᶠ ρ in 𝓝[>] 0, ∀ L n m, epsP ρ ≤ ‖mom L n‖ → epsP ρ ≤ ‖mom L m‖ →
      ‖mom L (n + m)‖ ≤ epsP ρ / 2 →
        |lam V w ρ L n - lam V w ρ L m| ≤ C / epsP ρ ^ 3 * ‖mom L (n + m)‖ := by
  obtain ⟨C, hC⟩ := scat_wmom_lipschitz hV hw 0
  refine ⟨C, ?_⟩
  filter_upwards [Lambda_eventually_small (δ := 1) one_pos] with ρ hρ'
  obtain ⟨hρ, hρ1, -⟩ := hρ'
  intro L n m hn hm hnm
  have he := Lambda_eps_pos hρ
  have he1 := Lambda_eps_le_one hρ hρ1.le
  have hn' := Lambda_not_PL_of_ge hρ hρ1 hn
  have hm' := Lambda_not_PL_of_ge hρ hρ1 hm
  rw [scat_lam_of_not_PL ρ L n hn', scat_lam_of_not_PL ρ L m hm',
    ← scat_wmom_neg hV hw (mom L m)]
  have hadd : mom L (n + m) = mom L n + mom L m := by
    ext i
    simp [mom, mul_add]
  have hq : ‖-mom L m - mom L n‖ = ‖mom L (n + m)‖ := by
    rw [hadd, ← norm_neg]
    congr 1
    abel
  have key := hC (epsP ρ) he he1 (mom L n) (-mom L m) hn (by rw [hq]; exact hnm)
  rw [hq] at key
  simp only [pow_zero, inv_one, mul_one] at key
  have : -wmom V w (mom L n) - -wmom V w (-mom L m) = wmom V w (-mom L m) - wmom V w (mom L n) := by
    ring
  rw [this]
  exact key

end

end LHYUpper
