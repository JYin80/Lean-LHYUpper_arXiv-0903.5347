module

public import LHYUpper.Model.Basic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section

namespace LHYUpper

/-! # The Gaussian potential and Born-integral bounds

Gaussian integral `∫ e^{-|x|²} dx = π^{3/2}`, the Gaussian as a Schwartz function, the radial
kernels `(4π r)⁻¹` on `r < 1` and `r ≥ 1`, and the bound `scat_born_split` for the Born integrand of
a bounded integrable potential obtained by splitting at `|x - y| = 1`. Shows that the Gaussian
potential `V(x) = e^{-|x|²}` satisfies the hypotheses of Theorem 2.1 [mainthm]
(`scat_gaussian_potentialHyp`). -/

/-- `∫_{ℝ³} e^{-|x|²} dx = π^{3/2}`. -/
theorem scat_gaussian_integral : ∫ x : R3, Real.exp (-‖x‖ ^ 2) = π ^ (3/2 : ℝ) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := R3) (b := 1) one_pos
  simpa [finrank_euclideanSpace_fin] using h

/-- The radial kernel `r ↦ (4π r)⁻¹` on `r < 1`, and `0` for `r ≥ 1`. -/
private def kernIn : ℝ → ℝ := Set.indicator (Set.Iio 1) (fun r => (4 * π * r)⁻¹)

private lemma kernIn_smul (y : ℝ) :
    y ^ (Module.finrank ℝ R3 - 1) • kernIn y =
      Set.indicator (Set.Iio 1) (fun y => y / (4 * π)) y := by
  rw [finrank_euclideanSpace_fin]
  by_cases hy : y < 1
  · simp only [kernIn, Set.indicator_of_mem (Set.mem_Iio.2 hy), smul_eq_mul]
    by_cases h0 : y = 0
    · simp [h0]
    · field_simp
  · simp [kernIn, Set.indicator_of_notMem (show y ∉ Set.Iio 1 from hy)]

private lemma kernIn_integrableOn :
    IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ R3 - 1) • kernIn y) (Set.Ioi 0) := by
  simp_rw [kernIn_smul]
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio]
  have h : IntegrableOn (fun y : ℝ => y / (4 * π)) (Set.Icc 0 1) :=
    (continuous_id.div_const _).integrableOn_Icc
  exact h.mono_set (fun x hx => ⟨hx.2.le, hx.1.le⟩)

private lemma kernIn_integrable : Integrable (fun z : R3 => kernIn ‖z‖) :=
  (integrable_fun_norm_addHaar volume).2 kernIn_integrableOn

private lemma kernIn_integral : ∫ z : R3, kernIn ‖z‖ = 1 / 2 := by
  rw [integral_fun_norm_addHaar volume kernIn]
  simp_rw [kernIn_smul]
  have hv : (volume : Measure R3).real (Metric.ball 0 1) = π * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  have hi : ∫ y in Set.Ioi (0:ℝ), Set.indicator (Set.Iio 1) (fun y => y / (4 * π)) y =
      1 / (8 * π) := by
    rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have : Set.Iio (1:ℝ) ∩ Set.Ioi 0 = Set.Ioo 0 1 := by
      ext x; simp [and_comm]
    rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    simp
    field_simp
    norm_num
  rw [hi, hv, finrank_euclideanSpace_fin]
  simp only [nsmul_eq_mul, smul_eq_mul]
  field_simp
  norm_num

/-- The radial kernel `r ↦ (4π r)⁻¹` on `r ≥ 1`, and `0` for `r < 1`. -/
private def kernOut : ℝ → ℝ := Set.indicator (Set.Ici 1) (fun r => (4 * π * r)⁻¹)

private lemma kernIn_add_kernOut (r : ℝ) : kernIn r + kernOut r = (4 * π * r)⁻¹ := by
  by_cases h : r < 1
  · simp [kernIn, kernOut, Set.indicator_of_mem (Set.mem_Iio.2 h),
      Set.indicator_of_notMem (show r ∉ Set.Ici 1 from not_le.2 h)]
  · simp [kernIn, kernOut, Set.indicator_of_notMem (show r ∉ Set.Iio 1 from h),
      Set.indicator_of_mem (Set.mem_Ici.2 (not_lt.1 h))]

private lemma kernIn_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ kernIn r := by
  unfold kernIn
  rw [Set.indicator_apply]
  split_ifs
  · positivity
  · exact le_rfl

private lemma kernOut_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ kernOut r := by
  unfold kernOut
  rw [Set.indicator_apply]
  split_ifs
  · positivity
  · exact le_rfl

private lemma kernOut_le (r : ℝ) : kernOut r ≤ (4 * π)⁻¹ := by
  unfold kernOut
  by_cases h : 1 ≤ r
  · rw [Set.indicator_of_mem (Set.mem_Ici.2 h)]
    have hpi := Real.pi_pos
    exact inv_anti₀ (by positivity) (le_mul_of_one_le_right (by positivity) h)
  · rw [Set.indicator_of_notMem (show r ∉ Set.Ici 1 from h)]
    positivity

private lemma measurable_kernIn : Measurable kernIn := by
  unfold kernIn
  exact (by fun_prop : Measurable fun r : ℝ => (4 * π * r)⁻¹).indicator measurableSet_Iio

private lemma measurable_kernOut : Measurable kernOut := by
  unfold kernOut
  exact (by fun_prop : Measurable fun r : ℝ => (4 * π * r)⁻¹).indicator measurableSet_Ici

open scoped ContDiff in
private lemma gaussian_iteratedFDeriv_le (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x : R3,
      ‖iteratedFDeriv ℝ n (fun x : R3 => Real.exp (-‖x‖ ^ 2)) x‖ ≤
        C * (1 + ‖x‖) ^ k * Real.exp (-‖x‖ ^ 2) := by
  obtain ⟨k, C, hC0, hC⟩ :=
    (Function.hasTemperateGrowth_norm_sq R3).norm_iteratedFDeriv_le_uniform n
  refine ⟨k * n, n.factorial * (1 + C) ^ n, by positivity, fun x => ?_⟩
  set D : ℝ := (1 + C) * (1 + ‖x‖) ^ k with hD
  have hD1 : 1 ≤ D := by
    have h1 : (1 : ℝ) ≤ 1 + C := by linarith
    have h2 : (1 : ℝ) ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ D := mul_le_mul h1 h2 zero_le_one (by linarith)
  have hq : ContDiff ℝ ∞ (fun x : R3 => -‖x‖ ^ 2) :=
    (Function.hasTemperateGrowth_norm_sq R3).1.neg
  have hexp : ContDiff ℝ ∞ Real.exp := Real.contDiff_exp
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := n) (N := ∞) (g := Real.exp)
    (f := fun x : R3 => -‖x‖ ^ 2) hexp hq (by exact_mod_cast le_top) x
    (C := Real.exp (-‖x‖ ^ 2)) (D := D) ?_ ?_
  · calc ‖iteratedFDeriv ℝ n (fun x : R3 => Real.exp (-‖x‖ ^ 2)) x‖
        ≤ n.factorial * Real.exp (-‖x‖ ^ 2) * D ^ n := key
      _ = (n.factorial * (1 + C) ^ n) * (1 + ‖x‖) ^ (k * n) * Real.exp (-‖x‖ ^ 2) := by
        rw [hD, mul_pow, ← pow_mul]; ring
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · intro i hi1 hin
    have h := hC i hin x
    have hneg : iteratedFDeriv ℝ i (fun x : R3 => -‖x‖ ^ 2) x
        = -iteratedFDeriv ℝ i (fun x : R3 => ‖x‖ ^ 2) x := by
      exact iteratedFDeriv_neg_apply (f := fun x : R3 => ‖x‖ ^ 2)
    rw [hneg, norm_neg]
    calc _ ≤ C * (1 + ‖x‖) ^ k := h
      _ ≤ D := by
        rw [hD]
        nlinarith [pow_nonneg (show (0:ℝ) ≤ 1 + ‖x‖ by linarith [norm_nonneg x]) k]
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)

private lemma gaussian_pow_mul_exp_le (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ p * Real.exp (-t ^ 2) ≤ p.factorial * Real.exp 2 := by
  have h1 : (1 + t) ^ p / p.factorial ≤ Real.exp (1 + t) :=
    Real.pow_div_factorial_le_exp (1 + t) (by linarith) p
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  have h2 : (1 + t) ^ p ≤ p.factorial * Real.exp (1 + t) := by
    rw [div_le_iff₀ hf] at h1; linarith
  have h3 : Real.exp (1 + t) * Real.exp (-t ^ 2) ≤ Real.exp 2 := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (t - 1/2)]
  calc (1 + t) ^ p * Real.exp (-t ^ 2) ≤ (p.factorial * Real.exp (1 + t)) * Real.exp (-t ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = p.factorial * (Real.exp (1 + t) * Real.exp (-t ^ 2)) := by ring
    _ ≤ p.factorial * Real.exp 2 := mul_le_mul_of_nonneg_left h3 hf.le

open scoped ContDiff in
/-- The Gaussian `x ↦ e^{-|x|²}` as a Schwartz function on `ℝ³`. -/
private def gaussianSchwartz : SchwartzMap R3 ℝ where
  toFun x := Real.exp (-‖x‖ ^ 2)
  smooth' := by
    have : ContDiff ℝ ∞ (fun x : R3 => -‖x‖ ^ 2) := (Function.hasTemperateGrowth_norm_sq R3).1.neg
    exact Real.contDiff_exp.comp this
  decay' := by
    intro k n
    obtain ⟨p, C, hC0, hC⟩ := gaussian_iteratedFDeriv_le n
    refine ⟨C * ((k + p).factorial * Real.exp 2), fun x => ?_⟩
    have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
      gcongr; linarith
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : R3 => Real.exp (-‖x‖ ^ 2)) x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ p * Real.exp (-‖x‖ ^ 2)) := by
          apply mul_le_mul h1 (hC x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + p) * Real.exp (-‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * ((k + p).factorial * Real.exp 2) :=
          mul_le_mul_of_nonneg_left (gaussian_pow_mul_exp_le _ _ (norm_nonneg _)) hC0

private lemma gaussian_born_lt_one : (1 / 2 + π ^ (3/2 : ℝ) / (4 * π) : ℝ) < 1 := by
  have h1 : π ^ (3/2 : ℝ) = π * Real.sqrt π := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have h2 : Real.sqrt π < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith [Real.pi_lt_four]
  rw [h1]
  have := Real.pi_pos
  rw [show π * Real.sqrt π / (4 * π) = Real.sqrt π / 4 by field_simp]
  linarith

/-- The part of the Born integrand over `|x - y| < 1`: it is integrable and its integral is at most
`M / 2`. -/
private lemma born_inner_part {V : R3 → ℝ} (M : ℝ) (hV0 : ∀ x, 0 ≤ V x) (hVM : ∀ x, V x ≤ M)
    (hVi : Integrable V) (x : R3) :
    Integrable (fun y => V y * kernIn ‖x - y‖) ∧ ∫ y, V y * kernIn ‖x - y‖ ≤ M / 2 := by
  have hk : Integrable (fun y : R3 => kernIn ‖x - y‖) := kernIn_integrable.comp_sub_left x
  have hk' : ∫ y : R3, kernIn ‖x - y‖ = 1 / 2 := by
    rw [integral_sub_left_eq_self (fun z : R3 => kernIn ‖z‖) volume x, kernIn_integral]
  have hm : Measurable fun y : R3 => kernIn ‖x - y‖ :=
    measurable_kernIn.comp (measurable_const.sub measurable_id).norm
  have hint : Integrable (fun y => V y * kernIn ‖x - y‖) := by
    refine (hk.const_mul M).mono' (hVi.aestronglyMeasurable.mul hm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h0 := kernIn_nonneg (norm_nonneg (x - y))
    rw [Real.norm_of_nonneg (mul_nonneg (hV0 y) h0)]
    exact mul_le_mul_of_nonneg_right (hVM y) h0
  refine ⟨hint, ?_⟩
  calc ∫ y, V y * kernIn ‖x - y‖ ≤ ∫ y, M * kernIn ‖x - y‖ := by
        refine integral_mono hint (hk.const_mul M) fun y => ?_
        exact mul_le_mul_of_nonneg_right (hVM y) (kernIn_nonneg (norm_nonneg _))
    _ = M / 2 := by rw [integral_const_mul, hk']; ring

/-- The part of the Born integrand over `|x - y| ≥ 1`: it is integrable and its integral is at most
`(∫ V) / (4π)`. -/
private lemma born_outer_part {V : R3 → ℝ} (hV0 : ∀ x, 0 ≤ V x) (hVi : Integrable V) (x : R3) :
    Integrable (fun y => V y * kernOut ‖x - y‖) ∧
      ∫ y, V y * kernOut ‖x - y‖ ≤ (∫ y, V y) / (4 * π) := by
  have hm : Measurable fun y : R3 => kernOut ‖x - y‖ :=
    measurable_kernOut.comp (measurable_const.sub measurable_id).norm
  have hb : Integrable (fun y => V y / (4 * π)) := hVi.div_const _
  have hle : ∀ y, V y * kernOut ‖x - y‖ ≤ V y / (4 * π) := fun y => by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (kernOut_le _) (hV0 y)
  have hint : Integrable (fun y => V y * kernOut ‖x - y‖) := by
    refine hb.mono' (hVi.aestronglyMeasurable.mul hm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hV0 y) (kernOut_nonneg (norm_nonneg _)))]
    exact hle y
  refine ⟨hint, ?_⟩
  calc ∫ y, V y * kernOut ‖x - y‖ ≤ ∫ y, V y / (4 * π) := integral_mono hint hb hle
    _ = (∫ y, V y) / (4 * π) := integral_div _ _

private lemma born_integrand_eq (V : R3 → ℝ) (x y : R3) :
    V y / (4 * π * ‖x - y‖) = V y * kernIn ‖x - y‖ + V y * kernOut ‖x - y‖ := by
  rw [← mul_add, kernIn_add_kernOut, div_eq_mul_inv]

/-- For `0 ≤ V ≤ M` integrable, splitting at `|x - y| = 1` gives
`∫ V(y) / (4π|x - y|) dy ≤ M/2 + (∫ V)/(4π)`: the smallness condition of Theorem 2.1 [mainthm]
in checkable form. -/
theorem scat_born_split {V : R3 → ℝ} (M : ℝ) (hV0 : ∀ x, 0 ≤ V x) (hVM : ∀ x, V x ≤ M)
    (hVi : Integrable V) (x : R3) :
    ∫ y, V y / (4 * π * ‖x - y‖) ≤ M / 2 + (∫ y, V y) / (4 * π) := by
  simp_rw [born_integrand_eq]
  obtain ⟨hA, hA'⟩ := born_inner_part M hV0 hVM hVi x
  obtain ⟨hB, hB'⟩ := born_outer_part hV0 hVi x
  rw [integral_add hA hB]
  exact add_le_add hA' hB'

/-- The Gaussian `x ↦ e^{-|x|²}` is integrable on `ℝ³`. -/
private lemma gaussian_integrable : Integrable (fun x : R3 => Real.exp (-‖x‖ ^ 2)) :=
  gaussianSchwartz.integrable

/-- The Gaussian potential `V(x) = e^{-|x|²}` satisfies the hypotheses of Theorem 2.1 [mainthm]:
Schwartz, even, nonnegative, not identically zero, and `sup_x ∫ V(y)/(4π|x - y|) dy < 1`. -/
theorem scat_gaussian_potentialHyp : PotentialHyp (fun x : R3 => Real.exp (-‖x‖ ^ 2)) := by
  refine ⟨⟨gaussianSchwartz, rfl⟩, fun x => by simp, fun x => (Real.exp_pos _).le,
    ⟨0, by simp⟩, ⟨1 / 2 + π ^ (3/2 : ℝ) / (4 * π), gaussian_born_lt_one, fun x => ?_⟩⟩
  have h := scat_born_split (V := fun x : R3 => Real.exp (-‖x‖ ^ 2)) 1
    (fun x => (Real.exp_pos _).le)
    (fun x => by simp) gaussian_integrable x
  rwa [scat_gaussian_integral] at h

end LHYUpper
