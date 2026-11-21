module

public import LHYUpper.Scattering.MomentumG
public import LHYUpper.Scattering.NewtonFourier

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # The momentum function `w_p = g_p / |p|²`

For `g = V(1 - w)` ((3.12) [gdef]) and the zero-energy scattering solution `w`, `w ∉ L¹`, so
`w_p` is defined by `w_p = g_p / |p|²` ((3.13) [gp]) rather than as a Fourier transform of `w`.
This file records that `w_p` is even, bounded by `g₀ / |p|²` and integrable, that
`w(x) = (2π)^{-3} ∫ w_p cos(p·x) dp`, the scattering equation in momentum space (3.11) [av], and a
mean-value bound for `p ↦ w_p` away from the origin. -/

/-- `w_p = g_p / |p|²`, (3.13) [gp]. -/
def wmom (V w : R3 → ℝ) (p : R3) : ℝ := (ft (gfun V w) p).re / ‖p‖ ^ 2

section Helpers
variable {V w : R3 → ℝ}

private lemma wm_ft_continuous (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Continuous (ft (gfun V w)) := by
  obtain ⟨S, hS⟩ := scat_ft_g_schwartz hV hw
  rw [← hS]
  exact S.continuous

private lemma wm_measurable (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Measurable (wmom V w) :=
  ((Complex.continuous_re.comp (wm_ft_continuous hV hw)).measurable).div
    (continuous_norm.pow 2).measurable

private lemma wm_abs_le_norm (p : R3) :
    |wmom V w p| ≤ ‖ft (gfun V w) p‖ / ‖p‖ ^ 2 := by
  unfold wmom
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p‖ ^ 2)]
  exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)

private lemma wm_integrable (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Integrable (wmom V w) := by
  obtain ⟨S, hS⟩ := scat_g_schwartz hV hw
  have h := (newton_eq_fourier S).1
  rw [hS] at h
  exact h.mono' (wm_measurable hV hw).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact wm_abs_le_norm p)

/-- `g_p / |p|²`, as a complex number, equals `w_p` (both sides vanish at `p = 0`). -/
private lemma wm_ft_div (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (p : R3) :
    ft (gfun V w) p / ((‖p‖ ^ 2 : ℝ) : ℂ) = ((wmom V w p : ℝ) : ℂ) := by
  rw [scat_ft_g_real hV hw p]
  unfold wmom
  push_cast
  rfl

/-- The inversion formula for `w` in complex form. -/
private lemma wm_inversion_complex (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (x : R3) :
    (w x : ℂ) = (((2 * π)⁻¹ ^ 3 : ℝ) : ℂ) *
      ∫ p, ((wmom V w p : ℝ) : ℂ) * Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) := by
  obtain ⟨S, hS⟩ := scat_g_schwartz hV hw
  have h := (newton_eq_fourier S).2.2 x
  rw [hS] at h
  have hn : newton (gfun V w) x = w x := (scat_w_newton hV hw x).symm
  rw [hn] at h
  rw [h, inv_pow]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [mul_div_assoc, wm_ft_div hV hw p, mul_comm]

private lemma wm_V_integrable (hV : PotentialHyp V) : Integrable V := by
  obtain ⟨S, hS⟩ := hV.schwartz
  rw [← hS]
  exact S.integrable

private lemma wm_V_continuous (hV : PotentialHyp V) : Continuous V := by
  obtain ⟨S, hS⟩ := hV.schwartz
  rw [← hS]
  exact S.continuous

/-- `(Vw)^_p = (2π)^{-3} ∫ V_{p-r} w_r dr`. -/
private lemma wm_ft_Vw (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (p : R3) :
    ft (fun x => V x * w x) p = (((2 * π)⁻¹ ^ 3 : ℝ) : ℂ) *
      ∫ r, ft V (p - r) * ((wmom V w r : ℝ) : ℂ) := by
  set F : R3 → R3 → ℂ := fun x r => ((wmom V w r : ℝ) : ℂ) *
    (Complex.exp (-(Complex.I * ((inner ℝ (p - r) x : ℝ) : ℂ))) * (V x : ℂ)) with hF
  have hVc := wm_V_continuous hV
  have hVi := wm_V_integrable hV
  have hwi := wm_integrable hV hw
  have hm := wm_measurable hV hw
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hF, Function.uncurry_def]
    have h1 : Measurable fun q : R3 × R3 => ((wmom V w q.2 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (hm.comp measurable_snd)
    have h2 : Continuous fun q : R3 × R3 => Complex.exp (-(Complex.I *
        ((inner ℝ (p - q.2) q.1 : ℝ) : ℂ))) := by fun_prop
    have h3 : Continuous fun q : R3 × R3 => ((V q.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hVc.comp continuous_fst)
    exact h1.mul (h2.measurable.mul h3.measurable)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (hVi.mul_prod hwi.abs).mono' hmeas (Eventually.of_forall fun q => ?_)
    obtain ⟨x, r⟩ := q
    simp only [hF, Function.uncurry_apply_pair]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hV.nonneg x)]
    have : ‖Complex.exp (-(Complex.I * ((inner ℝ (p - r) x : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [this]
    simp only [one_mul]
    ring_nf
    exact le_rfl
  have hB : ∀ x, Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * ((V x * w x : ℝ) : ℂ) =
      (((2 * π)⁻¹ ^ 3 : ℝ) : ℂ) * ∫ r, F x r := by
    intro x
    have h1 : ∫ r, F x r = Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * (V x : ℂ) *
        ∫ r, ((wmom V w r : ℝ) : ℂ) * Complex.exp (Complex.I * ((⟪r, x⟫ : ℝ) : ℂ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [hF]
      have : Complex.exp (-(Complex.I * ((inner ℝ (p - r) x : ℝ) : ℂ))) =
          Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) *
            Complex.exp (Complex.I * ((⟪r, x⟫ : ℝ) : ℂ)) := by
        rw [← Complex.exp_add, inner_sub_left]
        push_cast
        congr 1
        ring
      rw [this]
      ring
    rw [h1, Complex.ofReal_mul, wm_inversion_complex hV hw x]
    ring
  unfold ft
  have h2 : ∀ x, Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) *
      (((fun x => V x * w x) x : ℝ) : ℂ) = _ := hB
  simp_rw [h2]
  rw [integral_const_mul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  dsimp only
  simp only [hF]
  rw [integral_const_mul, mul_comm]

private lemma wm_ftV_continuous (hV : PotentialHyp V) : Continuous (ft V) := by
  obtain ⟨S, hS⟩ := scat_ft_V_schwartz hV
  rw [← hS]
  exact S.continuous

private lemma wm_ftV_mul_integrable (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    (p : R3) : Integrable (fun r => ft V (p - r) * ((wmom V w r : ℝ) : ℂ)) := by
  refine Integrable.bdd_mul (c := ∫ x, V x) (wm_integrable hV hw).ofReal ?_ ?_
  · exact ((wm_ftV_continuous hV).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun r => scat_ft_V_norm_le hV (p - r)

private lemma wm_phase_integrable {W : R3 → ℝ} (hW : Integrable W) (p : R3) :
    Integrable (fun x => Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * (W x : ℂ)) := by
  refine Integrable.bdd_mul (c := 1) hW.ofReal ?_ ?_
  · exact (by fun_prop : Continuous fun x : R3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ)))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Complex.norm_exp]
    simp

/-- `g_p = V_p - (Vw)^_p`. -/
private lemma wm_ft_g_sub (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (p : R3) :
    ft (gfun V w) p = ft V p - ft (fun x => V x * w x) p := by
  unfold ft
  rw [← integral_sub (wm_phase_integrable (wm_V_integrable hV) p)
    (wm_phase_integrable (scat_integrable hV hw).2.1 p)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  unfold gfun
  push_cast
  ring

/-- Derivative of the quotient `F(y) / |y|²` at `z ≠ 0`, with a bound on its norm. -/
private lemma wm_div_hasFDerivAt {F : R3 → ℝ} {F' : R3 →L[ℝ] ℝ} {z : R3} (hz : z ≠ 0)
    (hF : HasFDerivAt F F' z) :
    ∃ D : R3 →L[ℝ] ℝ, HasFDerivAt (fun y => F y / ‖y‖ ^ 2) D z ∧
      ‖D‖ ≤ ‖F'‖ / ‖z‖ ^ 2 + 2 * |F z| / ‖z‖ ^ 3 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hn2 : ‖z‖ ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun y : R3 => ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := (hasDerivAt_inv hn2).comp_hasFDerivAt z h1
  have h3 := hF.mul h2
  refine ⟨F z • ((-((‖z‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ z)) + (‖z‖ ^ 2)⁻¹ • F', ?_, ?_⟩
  · have : (fun y : R3 => F y / ‖y‖ ^ 2) = F * ((fun y : ℝ => y⁻¹) ∘ fun y : R3 => ‖y‖ ^ 2) := by
      funext y
      simp [div_eq_mul_inv]
    rw [this]
    exact h3
  · have e1 : ‖(2 : ℕ) • innerSL ℝ z‖ ≤ 2 * ‖z‖ := by
      refine norm_nsmul_le.trans ?_
      rw [innerSL_apply_norm]
      norm_num
    have e2 : ‖F z • ((-((‖z‖ ^ 2) ^ 2)⁻¹) • ((2 : ℕ) • innerSL ℝ z))‖ ≤
        |F z| * (((‖z‖ ^ 2) ^ 2)⁻¹ * (2 * ‖z‖)) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((‖z‖ ^ 2) ^ 2)⁻¹)]
      gcongr
    have e3 : ‖(‖z‖ ^ 2)⁻¹ • F'‖ = (‖z‖ ^ 2)⁻¹ * ‖F'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖z‖ ^ 2)⁻¹)]
    refine (norm_add_le _ _).trans ?_
    rw [e3]
    refine (add_le_add e2 le_rfl).trans (le_of_eq ?_)
    field_simp
    ring

end Helpers

section
variable {V w : R3 → ℝ}

/-- `w_{-p} = w_p`. -/
theorem scat_wmom_neg (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, wmom V w (-p) = wmom V w p := by
  intro p
  unfold wmom
  rw [scat_ft_g_neg hV hw, norm_neg]

/-- `|w_p| ≤ g₀/|p|²`. -/
theorem scat_wmom_abs_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, |wmom V w p| ≤ g0 V w / ‖p‖ ^ 2 := by
  intro p
  exact (wm_abs_le_norm p).trans
    (div_le_div_of_nonneg_right (scat_ft_g_norm_le hV hw p) (by positivity))

/-- `p ↦ w_p` is integrable on ℝ³. -/
theorem scat_wmom_integrable (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Integrable (wmom V w) :=
  wm_integrable hV hw

/-- Fourier inversion for `w`: `w(x) = (2π)^{-3} ∫ w_p cos(p·x) dp`. -/
theorem scat_w_inversion (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ x, w x = (2 * π)⁻¹ ^ 3 * ∫ p, wmom V w p * Real.cos ⟪p, x⟫ := by
  intro x
  have hint : Integrable (fun p => ((wmom V w p : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ))) := by
    refine Integrable.mul_bdd (c := 1) (scat_wmom_integrable hV hw).ofReal ?_ ?_
    · exact (by fun_prop : Continuous fun p : R3 => Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)))
        |>.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [mul_comm]
      exact (Complex.norm_exp_ofReal_mul_I _).le
  have h := congrArg Complex.re (wm_inversion_complex hV hw x)
  have hre : (∫ p, ((wmom V w p : ℝ) : ℂ) * Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ))).re =
      ∫ p, (((wmom V w p : ℝ) : ℂ) * Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ))).re :=
    (integral_re hint).symm
  rw [Complex.ofReal_re, Complex.re_ofReal_mul, hre] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [Complex.re_ofReal_mul, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]

/-- (3.13) [gp]: `g_p = |p|² w_p` for `p ≠ 0`. -/
theorem scat_gp (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, p ≠ 0 → ft (gfun V w) p = ((‖p‖ ^ 2 * wmom V w p : ℝ) : ℂ) := by
  intro p hp
  have h2 : ‖p‖ ^ 2 ≠ 0 := by positivity
  refine (scat_ft_g_real hV hw p).trans ?_
  congr 1
  unfold wmom
  field_simp

/-- (3.11) [av]: the scattering equation in momentum space, with `d³r/(2π)³`. -/
theorem scat_av (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, p ≠ 0 → -(‖p‖ ^ 2 * wmom V w p) + (ft V p).re
      - (2 * π)⁻¹ ^ 3 * ∫ r, (ft V (p - r)).re * wmom V w r = 0 := by
  intro p hp
  have h1 : ‖p‖ ^ 2 * wmom V w p = (ft (gfun V w) p).re := by
    have := congrArg Complex.re (scat_gp hV hw p hp)
    rw [Complex.ofReal_re] at this
    exact this.symm
  have h2 : (ft (fun x => V x * w x) p).re =
      (2 * π)⁻¹ ^ 3 * ∫ r, (ft V (p - r)).re * wmom V w r := by
    have hre : (∫ r, ft V (p - r) * ((wmom V w r : ℝ) : ℂ)).re =
        ∫ r, (ft V (p - r) * ((wmom V w r : ℝ) : ℂ)).re :=
      (integral_re (wm_ftV_mul_integrable hV hw p)).symm
    rw [wm_ft_Vw hV hw p, Complex.re_ofReal_mul, hre]
    simp only [Complex.re_mul_ofReal]
  have h3 := wm_ft_g_sub hV hw p
  have h4 := congrArg Complex.re h3
  rw [Complex.sub_re, h2] at h4
  rw [h1, h4]
  ring

/-- The mean-value bound for `w_p` used after (6.12) [proofubpsiu12] in the proof of Lemma 4.1 [lemkinetic]. -/
theorem scat_wmom_lipschitz (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (k : ℕ) :
    ∃ C, ∀ r, 0 < r → r ≤ 1 → ∀ p q : R3, r ≤ ‖p‖ → ‖q - p‖ ≤ r / 2 →
      |wmom V w q - wmom V w p| ≤ C / r ^ 3 * ((1 + ‖p‖) ^ k)⁻¹ * ‖q - p‖ := by
  obtain ⟨D0, hD0⟩ := scat_ft_g_decay hV hw k
  obtain ⟨D1, hD1⟩ := scat_fderiv_ft_g_decay hV hw k
  obtain ⟨S, hS⟩ := scat_ft_g_schwartz hV hw
  have hdiff : Differentiable ℝ (ft (gfun V w)) := by
    rw [← hS]
    exact S.differentiable
  have hD0nn : 0 ≤ D0 := le_trans (by positivity) (hD0 0)
  have hD1nn : 0 ≤ D1 := le_trans (by positivity) (hD1 0)
  refine ⟨2 ^ k * (4 * D1 + 16 * D0), fun r hr hr1 p q hrp hqp => ?_⟩
  set e : ℝ := ((1 + ‖p‖) ^ k)⁻¹ with he
  have hepos : 0 < e := by positivity
  have key : ∀ z ∈ Metric.closedBall p (r / 2), DifferentiableAt ℝ (wmom V w) z ∧
      ‖fderiv ℝ (wmom V w) z‖ ≤ 2 ^ k * (4 * D1 + 16 * D0) / r ^ 3 * e := by
    intro z hzmem
    rw [Metric.mem_closedBall, dist_eq_norm] at hzmem
    have hz1 : ‖p‖ / 2 ≤ ‖z‖ := by
      have : ‖p‖ ≤ ‖z‖ + ‖z - p‖ := by
        calc ‖p‖ = ‖z - (z - p)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖z‖ + ‖z - p‖ := norm_sub_le _ _
      linarith
    have hz2 : r / 2 ≤ ‖z‖ := by linarith
    have hzpos : 0 < ‖z‖ := by linarith
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    have hF : HasFDerivAt (fun y => (ft (gfun V w) y).re)
        (Complex.reCLM.comp (fderiv ℝ (ft (gfun V w)) z)) z :=
      Complex.reCLM.hasFDerivAt.comp z (hdiff z).hasFDerivAt
    obtain ⟨D, hD, hDn⟩ := wm_div_hasFDerivAt hz0 hF
    refine ⟨hD.differentiableAt, ?_⟩
    have hfd : fderiv ℝ (wmom V w) z = D := hD.fderiv
    rw [hfd]
    refine hDn.trans ?_
    -- decay at `z` in terms of decay at `p`
    have hdec : ((1 + ‖z‖) ^ k)⁻¹ ≤ 2 ^ k * e := by
      have h1 : 1 + ‖p‖ ≤ 2 * (1 + ‖z‖) := by linarith
      have h2 : (1 + ‖p‖) ^ k ≤ (2 * (1 + ‖z‖)) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
      rw [mul_pow] at h2
      have h3 : ((1 + ‖z‖) ^ k)⁻¹ ≤ ((1 + ‖p‖) ^ k / 2 ^ k)⁻¹ :=
        inv_anti₀ (by positivity) ((div_le_iff₀ (by positivity)).2 (by linarith [h2]))
      refine h3.trans (le_of_eq ?_)
      rw [inv_div, he, div_eq_mul_inv]
    have hA : ‖Complex.reCLM.comp (fderiv ℝ (ft (gfun V w)) z)‖ ≤ D1 * (2 ^ k * e) := by
      have h1 : ‖Complex.reCLM.comp (fderiv ℝ (ft (gfun V w)) z)‖ ≤
          ‖fderiv ℝ (ft (gfun V w)) z‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [Complex.reCLM_norm, one_mul]
      have h2 : ‖fderiv ℝ (ft (gfun V w)) z‖ ≤ D1 * ((1 + ‖z‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
        exact hD1 z
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hdec hD1nn))
    have hB : |(ft (gfun V w) z).re| ≤ D0 * (2 ^ k * e) := by
      have h1 : |(ft (gfun V w) z).re| ≤ ‖ft (gfun V w) z‖ := Complex.abs_re_le_norm _
      have h2 : ‖ft (gfun V w) z‖ ≤ D0 * ((1 + ‖z‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
        exact hD0 z
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hdec hD0nn))
    have hr3 : 0 < r ^ 3 := by positivity
    have hi2 : 1 / ‖z‖ ^ 2 ≤ 4 / r ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) hr3]
      have h1 : r ^ 3 ≤ r ^ 2 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
      have h2 : (r / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz2 2
      nlinarith
    have hi3 : 1 / ‖z‖ ^ 3 ≤ 8 / r ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) hr3]
      have h2 : (r / 2) ^ 3 ≤ ‖z‖ ^ 3 := pow_le_pow_left₀ (by positivity) hz2 3
      nlinarith
    have t1 : ‖Complex.reCLM.comp (fderiv ℝ (ft (gfun V w)) z)‖ / ‖z‖ ^ 2 ≤
        D1 * (2 ^ k * e) * (4 / r ^ 3) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hA hi2 (by positivity) (by positivity)
    have t2 : 2 * |(ft (gfun V w) z).re| / ‖z‖ ^ 3 ≤ 2 * (D0 * (2 ^ k * e)) * (8 / r ^ 3) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith) hi3 (by positivity) (by positivity)
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    field_simp
    ring
  have hmv := (convex_closedBall p (r / 2)).norm_image_sub_le_of_norm_fderiv_le (f := wmom V w)
    (fun z hz => (key z hz).1) (fun z hz => (key z hz).2)
    (Metric.mem_closedBall_self (by positivity))
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hqp)
  rw [Real.norm_eq_abs] at hmv
  exact hmv

end

end LHYUpper
