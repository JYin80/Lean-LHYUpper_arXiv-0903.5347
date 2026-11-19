import LHYUpper.Scattering.Newton

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # One derivative of the Newton potential

For continuous `h : ℝ³ → ℝ` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 3`, the Newton potential
`G ∗ h`, `G(z) = (4π|z|)⁻¹`, is `C¹`, its derivative is `∫ h(y) ∇G(x - y) dy` with
`∇G(z) = -z / (4π|z|³)`, and `‖D(G ∗ h)(x)‖ = O((1 + |x|)⁻²)`. These are the properties of the
scattering solution `w` of §2 (display after (2.1) [ham]) behind `‖∇w‖₂ < ∞`. The derivative is
the uniform limit of the derivatives of `G_δ ∗ h` with the smoothed kernel
`G_δ(z) = (4π (|z|² + δ²)^{1/2})⁻¹`, `δ → 0`. -/

/-! ### Weights -/

private lemma newtonDeriv_finrank : Module.finrank ℝ R3 = 3 := by simp

private lemma newtonDeriv_weight_pos (k : ℝ) (y : R3) : 0 < (1 + ‖y‖) ^ (-k) :=
  Real.rpow_pos_of_pos (by positivity) _

private lemma newtonDeriv_weight_le_one {k : ℝ} (hk : 0 ≤ k) (y : R3) : (1 + ‖y‖) ^ (-k) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)

private lemma newtonDeriv_weight_integrable {k : ℝ} (hk : 3 < k) :
    Integrable (fun y : R3 => (1 + ‖y‖) ^ (-k)) :=
  integrable_one_add_norm (by rw [newtonDeriv_finrank]; exact_mod_cast hk)

/-- `(1 + ‖a‖)^{-k} ≤ 2^k (1 + ‖b‖)^{-k}` when `‖a - b‖ ≤ 1`. -/
private lemma newtonDeriv_weight_shift {k : ℝ} (hk : 0 ≤ k) {a b : R3} (hab : ‖a - b‖ ≤ 1) :
    (1 + ‖a‖) ^ (-k) ≤ 2 ^ k * (1 + ‖b‖) ^ (-k) := by
  have h1 : 1 + ‖b‖ ≤ 2 * (1 + ‖a‖) := by
    have := norm_sub_norm_le b a
    rw [norm_sub_rev] at this
    linarith [norm_nonneg a]
  have h2 : (2 * (1 + ‖a‖)) ^ (-k) ≤ (1 + ‖b‖) ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    at h2
  have h3 : 0 < (2 : ℝ) ^ k := by positivity
  calc (1 + ‖a‖) ^ (-k) = 2 ^ k * ((2 ^ k)⁻¹ * (1 + ‖a‖) ^ (-k)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3.le

private lemma newtonDeriv_const_nonneg {h : R3 → ℝ} {k C : ℝ}
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) : 0 ≤ C := by
  have := hb 0
  simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
  linarith [abs_nonneg (h 0)]

private lemma newtonDeriv_abs_le {h : R3 → ℝ} {k C : ℝ} (hk : 0 ≤ k)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (y : R3) : |h y| ≤ C :=
  (hb y).trans (mul_le_of_le_one_right (newtonDeriv_const_nonneg hb)
    (newtonDeriv_weight_le_one hk y))

/-- `a^{-(m+2)} = a^{-2} a^{-m}` for `a > 0`. -/
private lemma newtonDeriv_rpow_split {a : ℝ} (ha : 0 < a) (m : ℝ) :
    a ^ (-(m + 2)) = (a ^ 2)⁻¹ * a ^ (-m) := by
  rw [show -(m + 2) = -2 + -m by ring, Real.rpow_add ha, Real.rpow_neg ha.le, Real.rpow_two]

/-! ### The kernel `‖z‖⁻²` -/

/-- The kernel `‖z‖⁻²` restricted to the closed unit ball. -/
private def newtonDerivLoc (z : R3) : ℝ :=
  (Metric.closedBall (0 : R3) 1).indicator (fun z => (‖z‖ ^ 2)⁻¹) z

private lemma newtonDerivLoc_nonneg (z : R3) : 0 ≤ newtonDerivLoc z := by
  unfold newtonDerivLoc
  exact Set.indicator_nonneg (fun z _ => by positivity) z

private lemma newtonDerivLoc_integrable : Integrable newtonDerivLoc := by
  have hloc : LocallyIntegrable (fun z : R3 => (‖z‖ ^ 2)⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 2)
      (by rw [newtonDeriv_finrank]; norm_num) (by rw [newtonDeriv_finrank]; norm_num)
      (Eventually.of_forall fun z => ?_)
      (by fun_prop : Measurable fun z : R3 => (‖z‖ ^ 2)⁻¹).aestronglyMeasurable
    rw [Real.norm_of_nonneg (by positivity), one_mul, Real.rpow_neg (norm_nonneg _),
      Real.rpow_two]
  exact (hloc.integrableOn_isCompact (isCompact_closedBall 0 1)).integrable_indicator
    Metric.isClosed_closedBall.measurableSet

private lemma newtonDeriv_inv_sq_le {r : ℝ} (hr : 1 < r) : (r ^ 2)⁻¹ ≤ 4 * ((1 + r) ^ 2)⁻¹ := by
  have h1 : 0 < r := by linarith
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `z ↦ ‖z‖⁻² (1 + ‖z‖)^{-m}` is integrable on ℝ³ for `m > 1`. -/
private lemma newtonDeriv_T_integrable {m : ℝ} (hm : 1 < m) :
    Integrable (fun z : R3 => (‖z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ (-m)) := by
  have hw : Integrable (fun z : R3 => (1 + ‖z‖) ^ (-(m + 2))) :=
    newtonDeriv_weight_integrable (by linarith)
  refine (newtonDerivLoc_integrable.add (hw.const_mul 4)).mono' ?_
    (Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : R3 => (‖z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ (-m))
      |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    unfold newtonDerivLoc
    by_cases hz : ‖z‖ ≤ 1
    · rw [Set.indicator_of_mem (by simpa using hz)]
      have h1 : (‖z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ (-m) ≤ (‖z‖ ^ 2)⁻¹ :=
        mul_le_of_le_one_right (by positivity) (newtonDeriv_weight_le_one (by linarith) z)
      have h2 : 0 ≤ 4 * (1 + ‖z‖) ^ (-(m + 2)) := by positivity
      linarith
    · rw [Set.indicator_of_notMem (by simpa using hz), zero_add,
        newtonDeriv_rpow_split (by positivity)]
      push Not at hz
      calc (‖z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ (-m) ≤ 4 * ((1 + ‖z‖) ^ 2)⁻¹ * (1 + ‖z‖) ^ (-m) :=
            mul_le_mul_of_nonneg_right (newtonDeriv_inv_sq_le hz) (newtonDeriv_weight_pos m z).le
        _ = _ := by ring

/-- Pointwise splitting behind the decay `O(|x|⁻²)`:
`(1 + |y|)^{-k} |x - y|⁻² ≤`
`4 (1 + |x|)⁻² ((1 + |y|)^{-k} + 4^{k-2} |x - y|⁻² (1 + |x - y|)^{-(k-2)})`. -/
private lemma newtonDeriv_pt {k : ℝ} (hk : 2 ≤ k) (x y : R3) :
    (1 + ‖y‖) ^ (-k) * (‖x - y‖ ^ 2)⁻¹ ≤
      4 / (1 + ‖x‖) ^ 2 * ((1 + ‖y‖) ^ (-k) +
        4 ^ (k - 2) * ((‖x - y‖ ^ 2)⁻¹ * (1 + ‖x - y‖) ^ (-(k - 2)))) := by
  have hR0 := norm_nonneg x
  have hd0 := norm_nonneg (x - y)
  have hr0 := norm_nonneg y
  have htri : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have := norm_add_le y (x - y)
    rwa [add_sub_cancel] at this
  set R := ‖x‖
  set d := ‖x - y‖
  set r := ‖y‖
  have hA : 0 < (1 + R) ^ 2 := by positivity
  have hw0 := newtonDeriv_weight_pos k y
  have hT0 : 0 ≤ 4 ^ (k - 2) * ((d ^ 2)⁻¹ * (1 + d) ^ (-(k - 2))) := by positivity
  by_cases hdR : (1 + R) / 2 ≤ d
  · have hdpos : 0 < d := by linarith
    have h1 : (d ^ 2)⁻¹ ≤ 4 / (1 + R) ^ 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hA]
      nlinarith
    calc (1 + r) ^ (-k) * (d ^ 2)⁻¹ ≤ (1 + r) ^ (-k) * (4 / (1 + R) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hw0.le
      _ = 4 / (1 + R) ^ 2 * (1 + r) ^ (-k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hT0) (by positivity)
  · push Not at hdR
    have h1 : (1 + R) / 2 ≤ 1 + r := by linarith
    have h2 : (1 + d) / 4 ≤ 1 + r := by linarith
    have hsplit : (1 + r) ^ (-k) = ((1 + r) ^ 2)⁻¹ * (1 + r) ^ (-(k - 2)) := by
      rw [← newtonDeriv_rpow_split (by positivity)]
      ring_nf
    have ha : ((1 + r) ^ 2)⁻¹ ≤ 4 / (1 + R) ^ 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hA]
      nlinarith
    have hb : (1 + r) ^ (-(k - 2)) ≤ 4 ^ (k - 2) * (1 + d) ^ (-(k - 2)) := by
      have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + d) / 4) h2
        (by linarith : -(k - 2) ≤ 0)
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
        div_inv_eq_mul] at this
      linarith
    rw [hsplit]
    calc ((1 + r) ^ 2)⁻¹ * (1 + r) ^ (-(k - 2)) * (d ^ 2)⁻¹
        ≤ 4 / (1 + R) ^ 2 * (4 ^ (k - 2) * (1 + d) ^ (-(k - 2))) * (d ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul ha hb (by positivity) (by positivity))
            (by positivity)
      _ = 4 / (1 + R) ^ 2 * (4 ^ (k - 2) * ((d ^ 2)⁻¹ * (1 + d) ^ (-(k - 2)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- `y ↦ (1 + |y|)^{-k} |x - y|⁻²` is integrable for `k > 3`. -/
private lemma newtonDeriv_P_integrable {k : ℝ} (hk : 3 < k) (x : R3) :
    Integrable (fun y : R3 => (1 + ‖y‖) ^ (-k) * (‖x - y‖ ^ 2)⁻¹) := by
  have hT := (newtonDeriv_T_integrable (m := k - 2) (by linarith)).comp_sub_left x
  have hD : Integrable (fun y : R3 => 4 / (1 + ‖x‖) ^ 2 * ((1 + ‖y‖) ^ (-k) +
      4 ^ (k - 2) * ((‖x - y‖ ^ 2)⁻¹ * (1 + ‖x - y‖) ^ (-(k - 2))))) :=
    ((newtonDeriv_weight_integrable hk).add (hT.const_mul _)).const_mul _
  refine hD.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (by fun_prop : Measurable fun y : R3 => (1 + ‖y‖) ^ (-k) * (‖x - y‖ ^ 2)⁻¹)
      |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact newtonDeriv_pt (by linarith) x y

/-! ### The kernel `∇G(z) = -z / (4π|z|³)` -/

/-- `∇G(z) = -z / (4π|z|³)` as a linear form. -/
private def newtonDerivK (z : R3) : R3 →L[ℝ] ℝ := -(4 * π * ‖z‖ ^ 3)⁻¹ • innerSL ℝ z

private lemma newtonDerivK_norm (z : R3) : ‖newtonDerivK z‖ = (4 * π)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  unfold newtonDerivK
  rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_of_nonneg (by positivity)]
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · simp [hz]
  · field_simp

private lemma newtonDerivK_aesm : AEStronglyMeasurable newtonDerivK volume := by
  unfold newtonDerivK
  exact (by fun_prop : Measurable fun z : R3 => -(4 * π * ‖z‖ ^ 3)⁻¹).aestronglyMeasurable.smul
    (innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ).continuous.aestronglyMeasurable

private lemma newtonDeriv_K_integrable {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    Integrable (fun y => h y • newtonDerivK (x - y)) := by
  refine ((newtonDeriv_P_integrable hk x).const_mul (C * (4 * π)⁻¹)).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact hh.aestronglyMeasurable.smul
      (newtonDerivK_aesm.comp_measurePreserving (Measure.measurePreserving_sub_left volume x))
  · rw [norm_smul, newtonDerivK_norm, Real.norm_eq_abs]
    calc |h y| * ((4 * π)⁻¹ * (‖x - y‖ ^ 2)⁻¹)
        ≤ C * (1 + ‖y‖) ^ (-k) * ((4 * π)⁻¹ * (‖x - y‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (hb y) (by positivity)
      _ = _ := by ring

/-! ### The smoothed kernel `G_δ(z) = (4π (|z|² + δ²)^{1/2})⁻¹` -/

private def newtonDerivG (δ : ℝ) (z : R3) : ℝ := (4 * π * √(‖z‖ ^ 2 + δ ^ 2))⁻¹

/-- `∇G_δ(z) = -z / (4π (|z|² + δ²)^{3/2})` as a linear form. -/
private def newtonDerivKδ (δ : ℝ) (z : R3) : R3 →L[ℝ] ℝ :=
  -(4 * π * √(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹ • innerSL ℝ z

private lemma newtonDeriv_sqrt_pos {δ : ℝ} (hδ : 0 < δ) (z : R3) : 0 < √(‖z‖ ^ 2 + δ ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

private lemma newtonDeriv_norm_le_sqrt (δ : ℝ) (z : R3) : ‖z‖ ≤ √(‖z‖ ^ 2 + δ ^ 2) := by
  calc ‖z‖ = √(‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

private lemma newtonDeriv_le_sqrt {δ : ℝ} (hδ : 0 < δ) (z : R3) : δ ≤ √(‖z‖ ^ 2 + δ ^ 2) := by
  calc δ = √(δ ^ 2) := (Real.sqrt_sq hδ.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖z‖])

private lemma newtonDerivG_hasFDerivAt {δ : ℝ} (hδ : 0 < δ) (z : R3) :
    HasFDerivAt (newtonDerivG δ) (newtonDerivKδ δ z) z := by
  have hpos : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have hs := newtonDeriv_sqrt_pos hδ z
  have h3 := (hasDerivAt_inv (by positivity : 4 * π * √(‖z‖ ^ 2 + δ ^ 2) ≠ 0)).comp_hasFDerivAt z
    ((((hasFDerivAt_id z).norm_sq.add_const (δ ^ 2)).sqrt (by simpa using hpos.ne')).const_mul
      (4 * π))
  have hs3 : √(‖z‖ ^ 2 + δ ^ 2) ^ 3 = √(‖z‖ ^ 2 + δ ^ 2) * (‖z‖ ^ 2 + δ ^ 2) := by
    rw [pow_succ, Real.sq_sqrt hpos.le, mul_comm]
  refine (h3.congr_fderiv ?_ : HasFDerivAt (newtonDerivG δ) _ z)
  ext v
  simp only [newtonDerivKδ, id_eq, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, ContinuousLinearMap.id_apply, nsmul_eq_mul, hs3]
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring

private lemma newtonDerivG_le {δ : ℝ} (hδ : 0 < δ) (z : R3) :
    newtonDerivG δ z ≤ (4 * π * δ)⁻¹ :=
  inv_anti₀ (by positivity) (by gcongr; exact newtonDeriv_le_sqrt hδ z)

private lemma newtonDerivG_le_newton (δ : ℝ) {z : R3} (hz : z ≠ 0) :
    newtonDerivG δ z ≤ (4 * π * ‖z‖)⁻¹ :=
  inv_anti₀ (by have := norm_pos_iff.2 hz; positivity)
    (by gcongr; exact newtonDeriv_norm_le_sqrt δ z)

private lemma newtonDerivG_nonneg (δ : ℝ) (z : R3) : 0 ≤ newtonDerivG δ z := by
  unfold newtonDerivG; positivity

private lemma newtonDerivKδ_norm_le {δ : ℝ} (hδ : 0 < δ) (z : R3) :
    ‖newtonDerivKδ δ z‖ ≤ (4 * π * δ ^ 2)⁻¹ := by
  have hs := newtonDeriv_sqrt_pos hδ z
  set s := √(‖z‖ ^ 2 + δ ^ 2)
  unfold newtonDerivKδ
  rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_of_nonneg (by positivity)]
  calc (4 * π * s ^ 3)⁻¹ * ‖z‖ ≤ (4 * π * s ^ 3)⁻¹ * s :=
        mul_le_mul_of_nonneg_left (newtonDeriv_norm_le_sqrt δ z) (by positivity)
    _ = (4 * π * s ^ 2)⁻¹ := by field_simp
    _ ≤ _ := inv_anti₀ (by positivity) (by gcongr; exact newtonDeriv_le_sqrt hδ z)

private lemma newtonDerivG_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (newtonDerivG δ) := by
  exact Continuous.inv₀ (f := fun z : R3 => 4 * π * √(‖z‖ ^ 2 + δ ^ 2)) (by fun_prop)
    fun z => (mul_pos (by positivity) (newtonDeriv_sqrt_pos hδ z)).ne'

private lemma newtonDerivKδ_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (newtonDerivKδ δ) := by
  exact (Continuous.inv₀ (f := fun z : R3 => 4 * π * √(‖z‖ ^ 2 + δ ^ 2) ^ 3) (by fun_prop)
    fun z => (mul_pos (by positivity) (pow_pos (newtonDeriv_sqrt_pos hδ z) 3)).ne').neg.smul
    (innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ).continuous

/-! ### The error `|∇G_δ - ∇G|` and its scaling -/

private def newtonDerivErr (δ : ℝ) (z : R3) : ℝ :=
  (4 * π)⁻¹ * (‖z‖ * ((‖z‖ ^ 3)⁻¹ - (√(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹))

private lemma newtonDerivErr_nonneg (δ : ℝ) (z : R3) : 0 ≤ newtonDerivErr δ z := by
  unfold newtonDerivErr
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · simp [hz]
  · have hr : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    have : (√(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹ ≤ (‖z‖ ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr; exact newtonDeriv_norm_le_sqrt δ z)
    have : 0 ≤ (‖z‖ ^ 3)⁻¹ - (√(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹ := by linarith
    positivity

private lemma newtonDerivKδ_sub_norm_le (δ : ℝ) (z : R3) :
    ‖newtonDerivKδ δ z - newtonDerivK z‖ ≤ newtonDerivErr δ z := by
  unfold newtonDerivKδ newtonDerivK
  refine (congrArg norm (sub_smul (-(4 * π * √(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹)
    (-(4 * π * ‖z‖ ^ 3)⁻¹) (innerSL ℝ z)).symm).trans_le ?_
  rw [norm_smul, innerSL_apply_norm]
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · rw [hz]; simp [newtonDerivErr, hz]
  · have hr : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    have hinv : (√(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹ ≤ (‖z‖ ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr; exact newtonDeriv_norm_le_sqrt δ z)
    have heq : -(4 * π * √(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹ - -(4 * π * ‖z‖ ^ 3)⁻¹ =
        (4 * π)⁻¹ * ((‖z‖ ^ 3)⁻¹ - (√(‖z‖ ^ 2 + δ ^ 2) ^ 3)⁻¹) := by
      rw [mul_inv, mul_inv]; ring
    rw [heq, Real.norm_of_nonneg (mul_nonneg (by positivity) (by linarith)), newtonDerivErr]
    apply le_of_eq
    ring

/-- `r ((r³)⁻¹ - ((r² + 1)^{3/2})⁻¹) ≤ 2 (r⁴)⁻¹` for `r > 0`. -/
private lemma newtonDeriv_err_alg {r : ℝ} (hr : 0 < r) :
    r * ((r ^ 3)⁻¹ - (√(r ^ 2 + 1 ^ 2) ^ 3)⁻¹) ≤ 2 * (r ^ 4)⁻¹ := by
  set s := √(r ^ 2 + 1 ^ 2) with hsdef
  have hs2 : s ^ 2 = r ^ 2 + 1 := by rw [hsdef, Real.sq_sqrt (by positivity)]; ring
  have hsr : r ≤ s := by
    have := Real.sqrt_le_sqrt (by nlinarith : r ^ 2 ≤ r ^ 2 + 1 ^ 2)
    rwa [Real.sqrt_sq hr.le] at this
  have hs : 0 < s := lt_of_lt_of_le hr hsr
  have hkey : (s + r) * (2 * s ^ 3 - r ^ 2 * (s ^ 3 - r ^ 3)) =
      2 * s ^ 3 * (s + r) - r ^ 2 * (s ^ 2 + s * r + r ^ 2) := by
    linear_combination (-(r ^ 2 * (s ^ 2 + s * r + r ^ 2))) * hs2
  have hrs2 : r ^ 2 ≤ s ^ 2 := by nlinarith
  have e1 : r ^ 2 * s ^ 2 ≤ s ^ 4 := by nlinarith
  have e2 : r ^ 4 ≤ s ^ 4 := by nlinarith
  have e3 : r ^ 3 * s ≤ s ^ 3 * r := by nlinarith [mul_pos hr hs]
  have hX : 0 ≤ 2 * s ^ 3 - r ^ 2 * (s ^ 3 - r ^ 3) := by
    have : 0 ≤ (s + r) * (2 * s ^ 3 - r ^ 2 * (s ^ 3 - r ^ 3)) := by rw [hkey]; nlinarith
    exact (mul_nonneg_iff_of_pos_left (by linarith)).1 this
  have hform : r * ((r ^ 3)⁻¹ - (s ^ 3)⁻¹) = (s ^ 3 - r ^ 3) / (r ^ 2 * s ^ 3) := by
    field_simp
  rw [hform, show 2 * (r ^ 4)⁻¹ = 2 / r ^ 4 by ring, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hX (sq_nonneg r)]

private lemma newtonDerivErr_one_le (z : R3) :
    newtonDerivErr 1 z ≤ (4 * π)⁻¹ * (newtonDerivLoc z + 32 * (1 + ‖z‖) ^ (-(4 : ℝ))) := by
  unfold newtonDerivErr newtonDerivLoc
  have hw : 0 ≤ (1 + ‖z‖) ^ (-(4 : ℝ)) := (newtonDeriv_weight_pos 4 z).le
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · rw [hz]
    have := newtonDerivLoc_nonneg z
    unfold newtonDerivLoc at this
    simp only [zero_mul, mul_zero]
    positivity
  have hr : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hinv : (√(‖z‖ ^ 2 + 1 ^ 2) ^ 3)⁻¹ ≥ 0 := by positivity
  by_cases hz1 : ‖z‖ ≤ 1
  · rw [Set.indicator_of_mem (by simpa using hz1)]
    have : ‖z‖ * (‖z‖ ^ 3)⁻¹ = (‖z‖ ^ 2)⁻¹ := by field_simp
    nlinarith
  · rw [Set.indicator_of_notMem (by simpa using hz1), zero_add]
    push Not at hz1
    refine (newtonDeriv_err_alg hr).trans ?_
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, show 2 * (‖z‖ ^ 4)⁻¹ = 2 / ‖z‖ ^ 4 by ring,
      show (32 : ℝ) * ((1 + ‖z‖) ^ 4)⁻¹ = 32 / (1 + ‖z‖) ^ 4 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 + ‖z‖) ^ 4 ≤ (2 * ‖z‖) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    nlinarith

private lemma newtonDerivErr_one_integrable : Integrable (newtonDerivErr 1) := by
  refine ((newtonDerivLoc_integrable.add ((newtonDeriv_weight_integrable (k := 4)
    (by norm_num)).const_mul 32)).const_mul (4 * π)⁻¹).mono' ?_
    (Eventually.of_forall fun z => ?_)
  · unfold newtonDerivErr
    exact (by fun_prop : Measurable fun z : R3 =>
      (4 * π)⁻¹ * (‖z‖ * ((‖z‖ ^ 3)⁻¹ - (√(‖z‖ ^ 2 + 1 ^ 2) ^ 3)⁻¹))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (newtonDerivErr_nonneg 1 z)]
    exact newtonDerivErr_one_le z

/-- Scaling: `E_δ(z) = δ⁻² E_1(z / δ)`. -/
private lemma newtonDerivErr_smul {δ : ℝ} (hδ : 0 < δ) (z : R3) :
    newtonDerivErr δ z = (δ ^ 2)⁻¹ * newtonDerivErr 1 (δ⁻¹ • z) := by
  unfold newtonDerivErr
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  have hs : √((δ⁻¹ * ‖z‖) ^ 2 + 1 ^ 2) = δ⁻¹ * √(‖z‖ ^ 2 + δ ^ 2) := by
    rw [← Real.sqrt_sq (inv_nonneg.2 hδ.le), ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
      (inv_nonneg.2 hδ.le)]
    congr 1
    field_simp
  rw [hs]
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · simp [hz]
  · have := newtonDeriv_sqrt_pos hδ z
    field_simp

private lemma newtonDerivErr_integrable {δ : ℝ} (hδ : 0 < δ) : Integrable (newtonDerivErr δ) := by
  rw [show newtonDerivErr δ = fun z => (δ ^ 2)⁻¹ * newtonDerivErr 1 (δ⁻¹ • z) from
    funext (newtonDerivErr_smul hδ)]
  exact (newtonDerivErr_one_integrable.comp_smul (inv_ne_zero hδ.ne')).const_mul _

private lemma newtonDerivErr_integral {δ : ℝ} (hδ : 0 < δ) :
    ∫ z, newtonDerivErr δ z = δ * ∫ z, newtonDerivErr 1 z := by
  rw [integral_congr_ae (Eventually.of_forall (newtonDerivErr_smul hδ)), integral_const_mul,
    Measure.integral_comp_smul, newtonDeriv_finrank, smul_eq_mul, inv_pow, inv_inv,
    abs_of_pos (by positivity)]
  field_simp

/-! ### The smoothed Newton potential -/

private def newtonDerivSm (δ : ℝ) (h : R3 → ℝ) (x : R3) : ℝ := ∫ y, h y * newtonDerivG δ (x - y)

private lemma newtonDerivKδ_integrable {h : R3 → ℝ} {k C δ : ℝ} (hδ : 0 < δ) (hk : 3 < k)
    (hh : Continuous h) (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    Integrable (fun y => h y • newtonDerivKδ δ (x - y)) := by
  refine (((newtonDeriv_weight_integrable hk).const_mul C).mul_const (4 * π * δ ^ 2)⁻¹).mono'
    (hh.smul ((newtonDerivKδ_continuous hδ).comp (continuous_const.sub continuous_id))
      |>.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hb y) (newtonDerivKδ_norm_le hδ _) (norm_nonneg _)
    (by have := newtonDeriv_const_nonneg hb; positivity)

private lemma newtonDerivSm_hasFDerivAt {h : R3 → ℝ} {k C δ : ℝ} (hδ : 0 < δ) (hk : 3 < k)
    (hh : Continuous h) (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    HasFDerivAt (newtonDerivSm δ h) (∫ y, h y • newtonDerivKδ δ (x - y)) x := by
  have hC := newtonDeriv_const_nonneg hb
  have hw := newtonDeriv_weight_integrable hk
  have hGc := newtonDerivG_continuous hδ
  have hKc := newtonDerivKδ_continuous hδ
  unfold newtonDerivSm
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x' y => h y * newtonDerivG δ (x' - y))
    (F' := fun x' y => h y • newtonDerivKδ δ (x' - y))
    (bound := fun y => C * (1 + ‖y‖) ^ (-k) * (4 * π * δ ^ 2)⁻¹)
    Filter.univ_mem (Eventually.of_forall fun x' => ?_) ?_ ?_ ?_
    ((hw.const_mul C).mul_const _) ?_
  · exact (hh.mul (hGc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine ((hw.const_mul C).mul_const (4 * π * δ)⁻¹).mono'
      (hh.mul (hGc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (newtonDerivG_nonneg _ _)]
    exact mul_le_mul (hb y) (newtonDerivG_le hδ _) (newtonDerivG_nonneg _ _) (by positivity)
  · exact (hh.smul (hKc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun y x' _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hb y) (newtonDerivKδ_norm_le hδ _) (norm_nonneg _) (by positivity)
  · refine Eventually.of_forall fun y x' _ => ?_
    have h1 : HasFDerivAt (fun x' => newtonDerivG δ (x' - y)) (newtonDerivKδ δ (x' - y)) x' := by
      have := (newtonDerivG_hasFDerivAt hδ (x' - y)).comp x' ((hasFDerivAt_id x').sub_const y)
      simp only [Function.comp_def, ContinuousLinearMap.comp_id, id] at this
      exact this
    exact h1.const_mul _

private lemma newtonDerivSm_tendsto {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    Tendsto (fun n : ℕ => newtonDerivSm (1 / ((n : ℝ) + 1)) h x) atTop (𝓝 (newton h x)) := by
  have hC := newtonDeriv_const_nonneg hb
  unfold newtonDerivSm newton
  refine tendsto_integral_of_dominated_convergence
    (fun y => C * ((4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k))) (fun n => ?_)
    ((newton_kernel_integrable hk x).const_mul C) (fun n => ?_) ?_
  · exact (hh.mul ((newtonDerivG_continuous (by positivity)).comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards [Measure.ae_ne volume x] with y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.2 hy.symm
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (newtonDerivG_nonneg _ _)]
    calc |h y| * newtonDerivG (1 / ((n : ℝ) + 1)) (x - y)
        ≤ C * (1 + ‖y‖) ^ (-k) * (4 * π * ‖x - y‖)⁻¹ :=
          mul_le_mul (hb y) (newtonDerivG_le_newton _ hxy)
            (newtonDerivG_nonneg _ _) (by positivity)
      _ = _ := by ring
  · filter_upwards [Measure.ae_ne volume x] with y hy
    have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hy.symm)
    have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => 4 * π * √(‖x - y‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) atTop
        (𝓝 (4 * π * ‖x - y‖)) := by
      have := ((tendsto_const_nhds (x := ‖x - y‖ ^ 2)).add (hδ.pow 2)).sqrt.const_mul (4 * π)
      simpa [Real.sqrt_sq (norm_nonneg _)] using this
    have h2 := (h1.inv₀ (by positivity)).const_mul (h y)
    simpa only [newtonDerivG, div_eq_mul_inv] using h2

/-! ### Uniform convergence of the derivatives -/

private lemma newtonDeriv_tendstoUniformly {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k)
    (hh : Continuous h) (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) :
    TendstoUniformly (fun (n : ℕ) (x : R3) => ∫ y, h y • newtonDerivKδ (1 / ((n : ℝ) + 1)) (x - y))
      (fun x => ∫ y, h y • newtonDerivK (x - y)) atTop := by
  have hC := newtonDeriv_const_nonneg hb
  set I := ∫ z, newtonDerivErr 1 z
  have hbound : ∀ δ : ℝ, 0 < δ → ∀ x : R3,
      ‖(∫ y, h y • newtonDerivK (x - y)) - ∫ y, h y • newtonDerivKδ δ (x - y)‖ ≤
        C * (δ * I) := by
    intro δ hδ x
    rw [← integral_sub (newtonDeriv_K_integrable hk hh hb x)
      (newtonDerivKδ_integrable hδ hk hh hb x)]
    have hE := ((newtonDerivErr_integrable hδ).comp_sub_left x).const_mul C
    calc ‖∫ y, (h y • newtonDerivK (x - y) - h y • newtonDerivKδ δ (x - y))‖
        ≤ ∫ y, C * newtonDerivErr δ (x - y) := by
          refine norm_integral_le_of_norm_le hE (Eventually.of_forall fun y => ?_)
          rw [show h y • newtonDerivK (x - y) - h y • newtonDerivKδ δ (x - y) =
              h y • (newtonDerivK (x - y) - newtonDerivKδ δ (x - y)) from (smul_sub _ _ _).symm,
            norm_smul, norm_sub_rev, Real.norm_eq_abs]
          exact mul_le_mul (newtonDeriv_abs_le (by linarith) hb y)
            (newtonDerivKδ_sub_norm_le δ _) (norm_nonneg _) hC
      _ = C * (δ * I) := by
          rw [integral_const_mul, integral_sub_left_eq_self (newtonDerivErr δ) volume x,
            newtonDerivErr_integral hδ]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1) * I)) atTop (𝓝 (C * (0 * I))) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const I).const_mul C
  rw [zero_mul, mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x
  rw [dist_eq_norm]
  exact (hbound _ (by positivity) x).trans_lt hn

private lemma newtonDeriv_hasFDerivAt_K {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    HasFDerivAt (newton h) (∫ y, h y • newtonDerivK (x - y)) x :=
  hasFDerivAt_of_tendstoUniformly (f := fun (n : ℕ) => newtonDerivSm (1 / ((n : ℝ) + 1)) h)
    (newtonDeriv_tendstoUniformly hk hh hb)
    (fun _ x => newtonDerivSm_hasFDerivAt (by positivity) hk hh hb x)
    (fun x => newtonDerivSm_tendsto hk hh hb x) x

private lemma newtonDeriv_L_continuous {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) :
    Continuous (fun x => ∫ y, h y • newtonDerivK (x - y)) := by
  have hC := newtonDeriv_const_nonneg hb
  have heq : ∀ x' : R3, ∫ y, h y • newtonDerivK (x' - y) = ∫ z, h (x' - z) • newtonDerivK z := by
    intro x'
    rw [← integral_sub_left_eq_self (fun y => h y • newtonDerivK (x' - y)) volume x']
    simp only [sub_sub_cancel]
  rw [show (fun x => ∫ y, h y • newtonDerivK (x - y)) = fun x' => ∫ z, h (x' - z) • newtonDerivK z
    from funext heq, continuous_iff_continuousAt]
  intro x
  refine continuousAt_of_dominated
    (bound := fun z => 2 ^ k * C * (4 * π)⁻¹ *
      ((1 + ‖x - z‖) ^ (-k) * (‖x - (x - z)‖ ^ 2)⁻¹))
    (Eventually.of_forall fun x' => ?_) ?_
    (((newtonDeriv_P_integrable hk x).comp_sub_left x).const_mul _)
    (Eventually.of_forall fun z => ?_)
  · exact (hh.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul
      newtonDerivK_aesm
  · filter_upwards [Metric.closedBall_mem_nhds x one_pos] with x' hx'
    refine Eventually.of_forall fun z => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    rw [norm_smul, newtonDerivK_norm, sub_sub_cancel, Real.norm_eq_abs]
    have hs := newtonDeriv_weight_shift (by linarith : 0 ≤ k) (a := x' - z) (b := x - z)
      (by rw [sub_sub_sub_cancel_right]; exact hx')
    calc |h (x' - z)| * ((4 * π)⁻¹ * (‖z‖ ^ 2)⁻¹)
        ≤ C * (2 ^ k * (1 + ‖x - z‖) ^ (-k)) * ((4 * π)⁻¹ * (‖z‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right ((hb _).trans (mul_le_mul_of_nonneg_left hs hC))
            (by positivity)
      _ = _ := by ring
  · exact ((hh.comp (continuous_id.sub continuous_const)).smul continuous_const).continuousAt

/-! ### One derivative gained for continuous densities -/

/-- For continuous `h` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 3`, the Newton potential `G ∗ h`
is `C¹` on ℝ³. -/
theorem newton_contDiff_one {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) : ContDiff ℝ 1 (newton h) := by
  have hf : fderiv ℝ (newton h) = fun x => ∫ y, h y • newtonDerivK (x - y) :=
    funext fun x => (newtonDeriv_hasFDerivAt_K hk hh hb x).fderiv
  refine contDiff_one_iff_fderiv.2
    ⟨fun x => (newtonDeriv_hasFDerivAt_K hk hh hb x).differentiableAt, ?_⟩
  rw [hf]
  exact newtonDeriv_L_continuous hk hh hb

/-- Decay of the gradient: for continuous `h` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 3`,
`‖D(G ∗ h)(x)‖ ≤ C' / (1 + |x|)²` for all `x ∈ ℝ³`. -/
theorem newton_fderiv_decay {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) :
    ∃ C', ∀ x : R3, ‖fderiv ℝ (newton h) x‖ ≤ C' / (1 + ‖x‖) ^ 2 := by
  have hC := newtonDeriv_const_nonneg hb
  have hT := newtonDeriv_T_integrable (m := k - 2) (by linarith)
  have hw := newtonDeriv_weight_integrable hk
  set c := ∫ y : R3, (1 + ‖y‖) ^ (-k)
  set t := ∫ z : R3, (‖z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ (-(k - 2))
  refine ⟨C * (4 * π)⁻¹ * 4 * (c + 4 ^ (k - 2) * t), fun x => ?_⟩
  rw [(newtonDeriv_hasFDerivAt_K hk hh hb x).fderiv]
  have hTx := hT.comp_sub_left x
  have hD : Integrable (fun y : R3 => C * (4 * π)⁻¹ * (4 / (1 + ‖x‖) ^ 2 *
      ((1 + ‖y‖) ^ (-k) + 4 ^ (k - 2) * ((‖x - y‖ ^ 2)⁻¹ * (1 + ‖x - y‖) ^ (-(k - 2)))))) :=
    ((hw.add (hTx.const_mul _)).const_mul _).const_mul _
  have hpt : ∀ y : R3, ‖h y • newtonDerivK (x - y)‖ ≤ C * (4 * π)⁻¹ * (4 / (1 + ‖x‖) ^ 2 *
      ((1 + ‖y‖) ^ (-k) + 4 ^ (k - 2) * ((‖x - y‖ ^ 2)⁻¹ * (1 + ‖x - y‖) ^ (-(k - 2))))) := by
    intro y
    rw [norm_smul, newtonDerivK_norm, Real.norm_eq_abs]
    calc |h y| * ((4 * π)⁻¹ * (‖x - y‖ ^ 2)⁻¹)
        ≤ C * (1 + ‖y‖) ^ (-k) * ((4 * π)⁻¹ * (‖x - y‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (hb y) (by positivity)
      _ = C * (4 * π)⁻¹ * ((1 + ‖y‖) ^ (-k) * (‖x - y‖ ^ 2)⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (newtonDeriv_pt (by linarith) x y) (by positivity)
  have hTs := integral_sub_left_eq_self
    (fun z : R3 => (‖z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ (-(k - 2))) volume x
  calc ‖∫ y, h y • newtonDerivK (x - y)‖
      ≤ ∫ y, C * (4 * π)⁻¹ * (4 / (1 + ‖x‖) ^ 2 *
          ((1 + ‖y‖) ^ (-k) + 4 ^ (k - 2) * ((‖x - y‖ ^ 2)⁻¹ * (1 + ‖x - y‖) ^ (-(k - 2))))) :=
        norm_integral_le_of_norm_le hD (Eventually.of_forall hpt)
    _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_add hw (hTx.const_mul _),
          integral_const_mul, hTs]
        ring

end LHYUpper
