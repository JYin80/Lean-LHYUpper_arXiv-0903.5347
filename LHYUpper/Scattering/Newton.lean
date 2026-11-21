module

public import LHYUpper.Model.Basic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section

namespace LHYUpper

/-- The Newton potential `(G ∗ h)(x) = ∫ h(y) / (4π|x - y|) dy` with `G(z) = (4π|z|)⁻¹`, the
fundamental solution of `-Δ` in ℝ³ used in §2 to construct `w`. -/
def newton (h : R3 → ℝ) (x : R3) : ℝ := ∫ y, h y / (4 * π * ‖x - y‖)

/-! ### Auxiliary estimates for the kernel `‖z‖⁻¹` -/

private lemma newton_finrank : Module.finrank ℝ R3 = 3 := by simp

/-- The kernel `‖z‖⁻¹` restricted to the closed unit ball. -/
private def newtonLocal (z : R3) : ℝ :=
  (Metric.closedBall (0 : R3) 1).indicator (fun z => ‖z‖⁻¹) z

private lemma newtonLocal_integrable : Integrable newtonLocal := by
  have hloc : LocallyIntegrable (fun z : R3 => ‖z‖⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by rw [newton_finrank]; norm_num)
      (by rw [newton_finrank]; norm_num) (Eventually.of_forall fun z => ?_)
      (measurable_norm.inv).aestronglyMeasurable
    simp [Real.rpow_neg_one]
  exact (hloc.integrableOn_isCompact (isCompact_closedBall 0 1)).integrable_indicator
    Metric.isClosed_closedBall.measurableSet

/-- `‖z‖⁻¹ u ≤ ‖z‖⁻¹ 1_{‖z‖ ≤ 1} + u` for `0 ≤ u ≤ 1`. -/
private lemma newton_inv_norm_mul_le (z : R3) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖z‖⁻¹ * u ≤ newtonLocal z + u := by
  unfold newtonLocal
  by_cases hz : ‖z‖ ≤ 1
  · rw [Set.indicator_of_mem (by simpa using hz)]
    have : ‖z‖⁻¹ * u ≤ ‖z‖⁻¹ := mul_le_of_le_one_right (inv_nonneg.2 (norm_nonneg _)) hu1
    linarith
  · rw [Set.indicator_of_notMem (by simpa using hz)]
    push Not at hz
    have : ‖z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz.le
    nlinarith

private lemma newton_weight_pos (k : ℝ) (y : R3) : 0 < (1 + ‖y‖) ^ (-k) :=
  Real.rpow_pos_of_pos (by positivity) _

private lemma newton_weight_le_one {k : ℝ} (hk : 0 ≤ k) (y : R3) : (1 + ‖y‖) ^ (-k) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)

private lemma newton_weight_integrable {k : ℝ} (hk : 3 < k) :
    Integrable (fun y : R3 => (1 + ‖y‖) ^ (-k)) :=
  integrable_one_add_norm (by rw [newton_finrank]; exact_mod_cast hk)

private lemma newton_kernel_le {k : ℝ} (hk : 0 ≤ k) (x y : R3) :
    (4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k) ≤
      (4 * π)⁻¹ * (newtonLocal (x - y) + (1 + ‖y‖) ^ (-k)) := by
  rw [mul_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (newton_inv_norm_mul_le _ (newton_weight_pos k y).le (newton_weight_le_one hk y))
    (by positivity)

/-- `(1 + ‖a‖)^{-k} ≤ 2^k (1 + ‖b‖)^{-k}` when `‖a - b‖ ≤ 1`. -/
private lemma newton_weight_shift {k : ℝ} (hk : 0 ≤ k) {a b : R3} (hab : ‖a - b‖ ≤ 1) :
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

private lemma newton_const_nonneg {h : R3 → ℝ} {k C : ℝ}
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) : 0 ≤ C := by
  have := hb 0
  simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
  linarith [abs_nonneg (h 0)]

/-- The Newton potential as `∫ G(z) h(x - z) dz`. -/
private lemma newton_eq_integral_sub (h : R3 → ℝ) (x : R3) :
    newton h x = ∫ z, (4 * π * ‖z‖)⁻¹ * h (x - z) := by
  rw [newton, ← integral_sub_left_eq_self (fun y => h y / (4 * π * ‖x - y‖)) volume x]
  simp only [sub_sub_cancel, div_eq_inv_mul]

/-- Domination of the translated integrand for `‖x' - x‖ ≤ 1`. -/
private lemma newton_shift_le {k C t : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C) {x x' z : R3}
    (hx : ‖x' - x‖ ≤ 1) (ht : t ≤ C * (1 + ‖x' - z‖) ^ (-k)) :
    (4 * π * ‖z‖)⁻¹ * t ≤
      2 ^ k * C * ((4 * π * ‖x - (x - z)‖)⁻¹ * (1 + ‖x - z‖) ^ (-k)) := by
  rw [sub_sub_cancel]
  have hs := newton_weight_shift hk (a := x' - z) (b := x - z)
    (by rw [sub_sub_sub_cancel_right]; exact hx)
  calc (4 * π * ‖z‖)⁻¹ * t ≤ (4 * π * ‖z‖)⁻¹ * (C * (1 + ‖x' - z‖) ^ (-k)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (4 * π * ‖z‖)⁻¹ * (C * (2 ^ k * (1 + ‖x - z‖) ^ (-k))) := by gcongr
    _ = _ := by ring

/-! ### Integrability of the kernel -/

/-- For `k > 3` and every `x ∈ ℝ³`, the function `y ↦ (4π|x - y|)⁻¹ (1 + |y|)^{-k}` is
integrable. -/
theorem newton_kernel_integrable {k : ℝ} (hk : 3 < k) (x : R3) :
    Integrable (fun y : R3 => (4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k)) := by
  have hS : Integrable (fun y : R3 => newtonLocal (x - y)) :=
    newtonLocal_integrable.comp_sub_left x
  refine ((hS.add (newton_weight_integrable hk)).const_mul (4 * π)⁻¹).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (by fun_prop : Measurable fun y : R3 => (4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k))
      |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact newton_kernel_le (by linarith) x y

/-- For `k > 3`, `sup_x ∫ (4π|x - y|)⁻¹ (1 + |y|)^{-k} dy < ∞`. -/
theorem newton_kernel_bound {k : ℝ} (hk : 3 < k) :
    ∃ K, ∀ x : R3, ∫ y, (4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k) ≤ K := by
  refine ⟨(4 * π)⁻¹ * ((∫ z, newtonLocal z) + ∫ y : R3, (1 + ‖y‖) ^ (-k)), fun x => ?_⟩
  have hS : Integrable (fun y : R3 => newtonLocal (x - y)) :=
    newtonLocal_integrable.comp_sub_left x
  have hw := newton_weight_integrable hk
  calc ∫ y, (4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k)
      ≤ ∫ y, (4 * π)⁻¹ * (newtonLocal (x - y) + (1 + ‖y‖) ^ (-k)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
          ((hS.add hw).const_mul _)
          (Eventually.of_forall fun y => newton_kernel_le (by linarith) x y)
    _ = _ := by
        rw [integral_const_mul, integral_add hS hw, integral_sub_left_eq_self newtonLocal volume x]

/-- For continuous `h` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 3`, the integrand
`y ↦ h(y) / (4π|x - y|)` of the Newton potential is integrable for every `x`. -/
theorem newton_integrable {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    Integrable (fun y => h y / (4 * π * ‖x - y‖)) := by
  refine ((newton_kernel_integrable hk x).const_mul C).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (hh.measurable.div (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * ‖x - y‖),
      div_eq_mul_inv]
    calc |h y| * (4 * π * ‖x - y‖)⁻¹ ≤ C * (1 + ‖y‖) ^ (-k) * (4 * π * ‖x - y‖)⁻¹ :=
          mul_le_mul_of_nonneg_right (hb y) (by positivity)
      _ = _ := by ring

/-- `|G ∗ h| ≤ C ∫ G(x - y) (1 + |y|)^{-k} dy`. -/
private lemma newton_abs_le {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    |newton h x| ≤ C * ∫ y, (4 * π * ‖x - y‖)⁻¹ * (1 + ‖y‖) ^ (-k) := by
  rw [← integral_const_mul, ← Real.norm_eq_abs, newton]
  refine norm_integral_le_of_norm_le ((newton_kernel_integrable hk x).const_mul C)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * ‖x - y‖),
    div_eq_mul_inv]
  calc |h y| * (4 * π * ‖x - y‖)⁻¹ ≤ C * (1 + ‖y‖) ^ (-k) * (4 * π * ‖x - y‖)⁻¹ :=
        mul_le_mul_of_nonneg_right (hb y) (by positivity)
    _ = _ := by ring

/-! ### Continuity -/

/-- For continuous `h` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 3`, the Newton potential `G ∗ h`
is continuous. -/
theorem newton_continuous {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) : Continuous (newton h) := by
  have hC := newton_const_nonneg hb
  rw [continuous_iff_continuousAt]
  intro x
  rw [show newton h = fun x' => ∫ z, (4 * π * ‖z‖)⁻¹ * h (x' - z) from
    funext (newton_eq_integral_sub h)]
  refine continuousAt_of_dominated
    (bound := fun z => 2 ^ k * C * ((4 * π * ‖x - (x - z)‖)⁻¹ * (1 + ‖x - z‖) ^ (-k)))
    (Eventually.of_forall fun x' => ?_) ?_
    (((newton_kernel_integrable hk x).comp_sub_left x).const_mul _)
    (Eventually.of_forall fun z => ?_)
  · exact ((by fun_prop : Measurable fun z : R3 => (4 * π * ‖z‖)⁻¹).mul
      (hh.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds x one_pos] with x' hx'
    refine Eventually.of_forall fun z => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * π * ‖z‖)⁻¹)]
    exact newton_shift_le (by linarith) hC hx' (hb _)
  · exact (continuous_const.mul (hh.comp (continuous_id.sub continuous_const))).continuousAt

/-! ### Decay and the leading term -/

/-- `t |‖x - y‖⁻¹ - ‖x‖⁻¹| ≤ 6‖x‖⁻² ‖y‖ t + 4C‖x‖⁻² ‖x - y‖⁻¹ (1 + ‖x - y‖)^{-(k-2)}` when
`0 ≤ t ≤ C (1 + ‖y‖)^{-k}`. -/
private lemma newton_asymp_pt {k C t : ℝ} (hk : 2 ≤ k) (hC : 0 ≤ C) {x y : R3} (hR : 0 < ‖x‖)
    (ht0 : 0 ≤ t) (ht : t ≤ C * (1 + ‖y‖) ^ (-k)) :
    t * |‖x - y‖⁻¹ - ‖x‖⁻¹| ≤
      6 / ‖x‖ ^ 2 * (‖y‖ * t) +
        4 * C / ‖x‖ ^ 2 * (‖x - y‖⁻¹ * (1 + ‖x - y‖) ^ (-(k - 2))) := by
  set R := ‖x‖ with hRdef
  set d := ‖x - y‖ with hd
  set r := ‖y‖ with hr
  have hd0 : 0 ≤ d := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have htri : |R - d| ≤ r := by
    have := abs_norm_sub_norm_le x (x - y)
    rwa [sub_sub_cancel] at this
  have hR2 : 0 < R ^ 2 := by positivity
  have hsecond : 0 ≤ 4 * C / R ^ 2 * (d⁻¹ * (1 + d) ^ (-(k - 2))) := by positivity
  by_cases hy : r ≤ R / 2
  · -- `|y| ≤ |x|/2`: `|d⁻¹ - R⁻¹| ≤ 2|y|/R²`.
    have hdR : R / 2 ≤ d := by
      have := (abs_le.1 htri).2
      linarith
    have hdpos : 0 < d := by linarith
    have key : |d⁻¹ - R⁻¹| ≤ 2 * r / R ^ 2 := by
      rw [inv_sub_inv hdpos.ne' hR.ne', abs_div, abs_of_pos (by positivity : 0 < d * R),
        div_le_div_iff₀ (by positivity) hR2]
      have h1 : |R - d| * R ^ 2 ≤ r * R ^ 2 := mul_le_mul_of_nonneg_right htri hR2.le
      have h2 : r * R ^ 2 ≤ 2 * r * (d * R) := by
        nlinarith [mul_le_mul_of_nonneg_left (show R ≤ 2 * d by linarith) (mul_nonneg hr0 hR.le)]
      linarith
    have : t * |d⁻¹ - R⁻¹| ≤ t * (2 * r / R ^ 2) := mul_le_mul_of_nonneg_left key ht0
    have h3 : t * (2 * r / R ^ 2) ≤ 6 / R ^ 2 * (r * t) := by
      rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hR2]
      nlinarith
    linarith
  · push Not at hy
    have hsplit : |d⁻¹ - R⁻¹| ≤ d⁻¹ + R⁻¹ := by
      have : 0 ≤ d⁻¹ := inv_nonneg.2 hd0
      have : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hRinv : R⁻¹ ≤ 2 * r / R ^ 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hR hR2]
      nlinarith
    have hfirst : t * R⁻¹ ≤ 2 / R ^ 2 * (r * t) := by
      calc t * R⁻¹ ≤ t * (2 * r / R ^ 2) := mul_le_mul_of_nonneg_left hRinv ht0
        _ = 2 / R ^ 2 * (r * t) := by ring
    by_cases hdR : R / 2 ≤ d
    · have hdpos : 0 < d := by linarith
      have hdinv : d⁻¹ ≤ 4 * r / R ^ 2 := by
        rw [inv_eq_one_div, div_le_div_iff₀ hdpos hR2]
        nlinarith
      have h4 : t * d⁻¹ ≤ 4 / R ^ 2 * (r * t) := by
        calc t * d⁻¹ ≤ t * (4 * r / R ^ 2) := mul_le_mul_of_nonneg_left hdinv ht0
          _ = 4 / R ^ 2 * (r * t) := by ring
      have : t * |d⁻¹ - R⁻¹| ≤ t * (d⁻¹ + R⁻¹) := mul_le_mul_of_nonneg_left hsplit ht0
      have h5 : 6 / R ^ 2 * (r * t) = 4 / R ^ 2 * (r * t) + 2 / R ^ 2 * (r * t) := by ring
      nlinarith
    · push Not at hdR
      have hdr : d ≤ r := by linarith
      have hw : (1 + r) ^ (-k) ≤ 4 / R ^ 2 * (1 + d) ^ (-(k - 2)) := by
        have hsplitk : (1 + r) ^ (-k) = (1 + r) ^ (-2 : ℝ) * (1 + r) ^ (-(k - 2)) := by
          rw [← Real.rpow_add (by positivity)]
          ring_nf
        rw [hsplitk]
        have ha : (1 + r) ^ (-2 : ℝ) ≤ 4 / R ^ 2 := by
          rw [Real.rpow_neg (by positivity), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast, inv_eq_one_div, div_le_div_iff₀ (by positivity) hR2]
          nlinarith
        have hb2 : (1 + r) ^ (-(k - 2)) ≤ (1 + d) ^ (-(k - 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        exact mul_le_mul ha hb2 (by positivity) (by positivity)
      have h6 : t * d⁻¹ ≤ 4 * C / R ^ 2 * (d⁻¹ * (1 + d) ^ (-(k - 2))) := by
        calc t * d⁻¹ ≤ C * (1 + r) ^ (-k) * d⁻¹ :=
              mul_le_mul_of_nonneg_right ht (inv_nonneg.2 hd0)
          _ ≤ C * (4 / R ^ 2 * (1 + d) ^ (-(k - 2))) * d⁻¹ := by gcongr
          _ = _ := by ring
      have : t * |d⁻¹ - R⁻¹| ≤ t * (d⁻¹ + R⁻¹) := mul_le_mul_of_nonneg_left hsplit ht0
      have h7 : 2 / R ^ 2 * (r * t) ≤ 6 / R ^ 2 * (r * t) := by
        gcongr
        norm_num
      nlinarith

/-- `z ↦ ‖z‖⁻¹ (1 + ‖z‖)^{-m}` is integrable for `m > 2`. -/
private lemma newton_inv_norm_weight_integrable {m : ℝ} (hm : 2 < m) :
    Integrable (fun z : R3 => ‖z‖⁻¹ * (1 + ‖z‖) ^ (-m)) := by
  have hw : Integrable (fun z : R3 => (1 + ‖z‖) ^ (-(m + 1))) :=
    newton_weight_integrable (by linarith)
  refine (newtonLocal_integrable.add (hw.const_mul 2)).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : R3 => ‖z‖⁻¹ * (1 + ‖z‖) ^ (-m)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have hsplit : (1 + ‖z‖) ^ (-(m + 1)) = (1 + ‖z‖)⁻¹ * (1 + ‖z‖) ^ (-m) := by
      rw [show -(m + 1) = -1 + -m by ring, Real.rpow_add (by positivity), Real.rpow_neg_one]
    simp only [Pi.add_apply]
    rw [hsplit]
    unfold newtonLocal
    by_cases hz : ‖z‖ ≤ 1
    · rw [Set.indicator_of_mem (by simpa using hz)]
      have h1 : ‖z‖⁻¹ * (1 + ‖z‖) ^ (-m) ≤ ‖z‖⁻¹ :=
        mul_le_of_le_one_right (inv_nonneg.2 (norm_nonneg _))
          (newton_weight_le_one (by linarith) z)
      have h2 : 0 ≤ 2 * ((1 + ‖z‖)⁻¹ * (1 + ‖z‖) ^ (-m)) := by positivity
      linarith
    · rw [Set.indicator_of_notMem (by simpa using hz), zero_add]
      push Not at hz
      have h1 : ‖z‖⁻¹ ≤ 2 * (1 + ‖z‖)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ (by linarith)
          (by linarith)]
        linarith
      calc ‖z‖⁻¹ * (1 + ‖z‖) ^ (-m) ≤ 2 * (1 + ‖z‖)⁻¹ * (1 + ‖z‖) ^ (-m) :=
            mul_le_mul_of_nonneg_right h1 (newton_weight_pos m z).le
        _ = _ := by ring

/-- For continuous `h` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 4`, the Newton potential has the
leading term `(∫ h) / (4π|x|)` with error `O(|x|⁻²)`:
`|(G ∗ h)(x) - (∫ h) / (4π|x|)| ≤ C'' / |x|²` for `|x| ≥ 1`. -/
theorem newton_asymp {h : R3 → ℝ} {k C : ℝ} (hk : 4 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) :
    ∃ C'', ∀ x : R3, 1 ≤ ‖x‖ →
      |newton h x - (∫ y, h y) / (4 * π * ‖x‖)| ≤ C'' / ‖x‖ ^ 2 := by
  have hC := newton_const_nonneg hb
  have hint := newton_integrable (by linarith) hh hb
  have hhint : Integrable h := by
    refine ((newton_weight_integrable (k := k) (by linarith)).const_mul C).mono'
      hh.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact hb y
  have hM : Integrable (fun y : R3 => ‖y‖ * |h y|) := by
    refine ((newton_weight_integrable (k := k - 1) (by linarith)).const_mul C).mono'
      (by fun_prop) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), show -(k - 1) = 1 + -k by ring,
      Real.rpow_add (by positivity), Real.rpow_one]
    calc ‖y‖ * |h y| ≤ (1 + ‖y‖) * (C * (1 + ‖y‖) ^ (-k)) :=
          mul_le_mul (by linarith) (hb y) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hT := newton_inv_norm_weight_integrable (m := k - 2) (by linarith)
  set T : R3 → ℝ := fun z => ‖z‖⁻¹ * (1 + ‖z‖) ^ (-(k - 2)) with hTdef
  refine ⟨(4 * π)⁻¹ * (6 * ∫ y, ‖y‖ * |h y|) + (4 * π)⁻¹ * (4 * C * ∫ z, T z), fun x hx => ?_⟩
  have hR : 0 < ‖x‖ := by linarith
  have hTx : Integrable (fun y => T (x - y)) := hT.comp_sub_left x
  have heq : newton h x - (∫ y, h y) / (4 * π * ‖x‖) =
      ∫ y, (h y / (4 * π * ‖x - y‖) - h y / (4 * π * ‖x‖)) := by
    rw [newton, ← integral_div, integral_sub (hint x) (hhint.div_const _)]
  have hP : Integrable (fun y => (4 * π)⁻¹ *
      (6 / ‖x‖ ^ 2 * (‖y‖ * |h y|) + 4 * C / ‖x‖ ^ 2 * T (x - y))) :=
    ((hM.const_mul _).add (hTx.const_mul _)).const_mul _
  rw [heq, ← Real.norm_eq_abs]
  calc ‖∫ y, (h y / (4 * π * ‖x - y‖) - h y / (4 * π * ‖x‖))‖
      ≤ ∫ y, (4 * π)⁻¹ * (6 / ‖x‖ ^ 2 * (‖y‖ * |h y|) + 4 * C / ‖x‖ ^ 2 * T (x - y)) := by
        refine norm_integral_le_of_norm_le hP (Eventually.of_forall fun y => ?_)
        have hform : h y / (4 * π * ‖x - y‖) - h y / (4 * π * ‖x‖) =
            (4 * π)⁻¹ * (h y * (‖x - y‖⁻¹ - ‖x‖⁻¹)) := by
          simp only [div_eq_mul_inv, mul_inv]
          ring
        rw [hform, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹)]
        exact mul_le_mul_of_nonneg_left
          (newton_asymp_pt (by linarith) hC hR (abs_nonneg _) (hb y)) (by positivity)
    _ = ((4 * π)⁻¹ * (6 * ∫ y, ‖y‖ * |h y|) + (4 * π)⁻¹ * (4 * C * ∫ z, T z)) / ‖x‖ ^ 2 := by
        rw [integral_const_mul, integral_add (hM.const_mul _) (hTx.const_mul _),
          integral_const_mul, integral_const_mul, integral_sub_left_eq_self T volume x]
        field_simp

/-- For continuous `h` with `|h(y)| ≤ C (1 + |y|)^{-k}`, `k > 4`, the Newton potential decays:
`|(G ∗ h)(x)| ≤ C' / (1 + |x|)`. -/
theorem newton_decay {h : R3 → ℝ} {k C : ℝ} (hk : 4 < k) (hh : Continuous h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k)) :
    ∃ C', ∀ x : R3, |newton h x| ≤ C' / (1 + ‖x‖) := by
  obtain ⟨K, hK⟩ := newton_kernel_bound (k := k) (by linarith)
  obtain ⟨C'', hC''⟩ := newton_asymp hk hh hb
  have hC := newton_const_nonneg hb
  have hbd : ∀ x, |newton h x| ≤ C * K := fun x =>
    (newton_abs_le (by linarith) hb x).trans (mul_le_mul_of_nonneg_left (hK x) hC)
  set A := |∫ y, h y| / (4 * π) with hA
  refine ⟨max (2 * (C * K)) (2 * (A + C'')), fun x => ?_⟩
  have hx1 : 0 < 1 + ‖x‖ := by positivity
  rw [le_div_iff₀ hx1]
  by_cases hx : ‖x‖ ≤ 1
  · have hCK : 0 ≤ C * K := (abs_nonneg _).trans (hbd x)
    calc |newton h x| * (1 + ‖x‖) ≤ C * K * 2 := by
          have := hbd x
          have := abs_nonneg (newton h x)
          nlinarith
      _ ≤ _ := by rw [mul_comm]; exact le_max_left _ _
  · push Not at hx
    have hR : 0 < ‖x‖ := by linarith
    have h1 := hC'' x hx.le
    have hC''0 : 0 ≤ C'' := by
      by_contra hneg
      push Not at hneg
      have : C'' / ‖x‖ ^ 2 < 0 := div_neg_of_neg_of_pos hneg (by positivity)
      linarith [abs_nonneg (newton h x - (∫ y, h y) / (4 * π * ‖x‖))]
    have h2 : |newton h x| ≤ A / ‖x‖ + C'' / ‖x‖ ^ 2 := by
      have := abs_sub_abs_le_abs_sub (newton h x) ((∫ y, h y) / (4 * π * ‖x‖))
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * π * ‖x‖), hA, div_div] at *
      linarith
    have h3 : C'' / ‖x‖ ^ 2 ≤ C'' / ‖x‖ := by
      apply div_le_div_of_nonneg_left hC''0 hR
      nlinarith
    have h4 : |newton h x| * ‖x‖ ≤ A + C'' := by
      have : |newton h x| ≤ (A + C'') / ‖x‖ := by rw [add_div]; linarith
      rwa [le_div_iff₀ hR] at this
    have hA0 : 0 ≤ A := by positivity
    calc |newton h x| * (1 + ‖x‖) ≤ (A + C'') * 2 := by nlinarith [abs_nonneg (newton h x)]
      _ ≤ _ := by rw [mul_comm]; exact le_max_right _ _

/-! ### Differentiation under the integral -/

/-- For `h ∈ C¹` with `|h(y)|, ‖Dh(y)‖ ≤ C (1 + |y|)^{-k}`, `k > 3`, the Newton potential is
differentiable at every `x` with derivative `∫ (4π|x - y|)⁻¹ Dh(y) dy`. -/
theorem newton_hasFDerivAt {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : ContDiff ℝ 1 h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k))
    (hd : ∀ y, ‖fderiv ℝ h y‖ ≤ C * (1 + ‖y‖) ^ (-k)) (x : R3) :
    HasFDerivAt (newton h) (∫ y, (4 * π * ‖x - y‖)⁻¹ • fderiv ℝ h y) x := by
  have hC := newton_const_nonneg hb
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hcont' : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have heq : ∫ y, (4 * π * ‖x - y‖)⁻¹ • fderiv ℝ h y =
      ∫ z, (4 * π * ‖z‖)⁻¹ • fderiv ℝ h (x - z) := by
    rw [← integral_sub_left_eq_self (fun y => (4 * π * ‖x - y‖)⁻¹ • fderiv ℝ h y) volume x]
    simp only [sub_sub_cancel]
  rw [show newton h = fun x' => ∫ z, (4 * π * ‖z‖)⁻¹ * h (x' - z) from
    funext (newton_eq_integral_sub h), heq]
  have hmeasG : Measurable fun z : R3 => (4 * π * ‖z‖)⁻¹ := by fun_prop
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x' z => (4 * π * ‖z‖)⁻¹ • fderiv ℝ h (x' - z))
    (bound := fun z => 2 ^ k * C * ((4 * π * ‖x - (x - z)‖)⁻¹ * (1 + ‖x - z‖) ^ (-k)))
    (Metric.closedBall_mem_nhds x one_pos) (Eventually.of_forall fun x' => ?_) ?_ ?_ ?_
    (((newton_kernel_integrable hk x).comp_sub_left x).const_mul _) ?_
  · exact (hmeasG.mul (hh.continuous.comp
      (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable
  · have := (newton_integrable hk hh.continuous hb x).comp_sub_left x
    simp only [sub_sub_cancel] at this
    exact this.congr (Eventually.of_forall fun z => by simp only [div_eq_inv_mul])
  · exact hmeasG.aestronglyMeasurable.smul
      (hcont'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun z x' hx' => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact newton_shift_le (by linarith) hC hx' (hd _)
  · refine Eventually.of_forall fun z x' _ => ?_
    have h1 : HasFDerivAt (fun x' => h (x' - z)) (fderiv ℝ h (x' - z)) x' := by
      have := (hdiff (x' - z)).hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const z)
      simp only [Function.comp_def, ContinuousLinearMap.comp_id, id] at this
      exact this
    exact h1.const_mul _

/-- Per direction, `D(G ∗ h)(x) v = (G ∗ (Dh · v))(x)` under the hypotheses of
`newton_hasFDerivAt`. -/
theorem newton_fderiv_apply {h : R3 → ℝ} {k C : ℝ} (hk : 3 < k) (hh : ContDiff ℝ 1 h)
    (hb : ∀ y, |h y| ≤ C * (1 + ‖y‖) ^ (-k))
    (hd : ∀ y, ‖fderiv ℝ h y‖ ≤ C * (1 + ‖y‖) ^ (-k)) (x v : R3) :
    fderiv ℝ (newton h) x v = newton (fun y => fderiv ℝ h y v) x := by
  have hcont' : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have hI : Integrable (fun y => (4 * π * ‖x - y‖)⁻¹ • fderiv ℝ h y) := by
    refine ((newton_kernel_integrable hk x).const_mul C).mono' ?_
      (Eventually.of_forall fun y => ?_)
    · exact (by fun_prop : Measurable fun y : R3 => (4 * π * ‖x - y‖)⁻¹).aestronglyMeasurable.smul
        hcont'.aestronglyMeasurable
    · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (4 * π * ‖x - y‖)⁻¹ * ‖fderiv ℝ h y‖ ≤ (4 * π * ‖x - y‖)⁻¹ * (C * (1 + ‖y‖) ^ (-k)) :=
            mul_le_mul_of_nonneg_left (hd y) (by positivity)
        _ = _ := by ring
  rw [(newton_hasFDerivAt hk hh hb hd x).fderiv, ContinuousLinearMap.integral_apply hI]
  simp only [newton, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

end LHYUpper
