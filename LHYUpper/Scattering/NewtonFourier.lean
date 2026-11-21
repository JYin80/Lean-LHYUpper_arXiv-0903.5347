module

public import LHYUpper.Scattering.Newton
public import LHYUpper.Scattering.FourierBasic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! ### Schwartz bounds -/

/-- A Schwartz function decays faster than every power. -/
private lemma nf_schwartz_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : SchwartzMap R3 E) (k : ℕ) : ∃ C, ∀ y, (1 + ‖y‖) ^ k * ‖S y‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
    fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl S y
  rwa [norm_iteratedFDeriv_zero] at h

/-- `|g(y)| ≤ C (1 + |y|)^{-4}` for a Schwartz function `g`. -/
private lemma nf_g_bound (g : SchwartzMap R3 ℝ) :
    ∃ C, ∀ y, |g y| ≤ C * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  obtain ⟨C, hC⟩ := nf_schwartz_decay g 4
  refine ⟨C, fun y => ?_⟩
  have h := hC y
  have hp : 0 < (1 + ‖y‖) ^ 4 := by positivity
  rw [Real.rpow_neg (by positivity), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp, ← Real.norm_eq_abs, mul_comm]
  exact h

/-- The complex-valued Schwartz function `x ↦ (g x : ℂ)`. -/
private def nfC (g : SchwartzMap R3 ℝ) : SchwartzMap R3 ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM g

/-- The scaling `p ↦ (2π)⁻¹ p`. -/
private def nfScale : R3 ≃L[ℝ] R3 :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity))

/-- `p ↦ g_p` as a Schwartz function. -/
private def nfFt (g : SchwartzMap R3 ℝ) : SchwartzMap R3 ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ nfScale (𝓕 (nfC g))

private lemma nfFt_apply (g : SchwartzMap R3 ℝ) (p : R3) : nfFt g p = ft (g : R3 → ℝ) p := by
  change 𝓕 (fun x => (g x : ℂ)) (nfScale p) = ft g p
  rw [scat_ft_eq_fourier]
  rfl

private lemma nf_ft_continuous (g : SchwartzMap R3 ℝ) : Continuous (ft (g : R3 → ℝ)) := by
  have h : ft (g : R3 → ℝ) = nfFt g := funext fun p => (nfFt_apply g p).symm
  rw [h]
  exact (nfFt g).continuous

private lemma nf_ft_decay (g : SchwartzMap R3 ℝ) (k : ℕ) :
    ∃ C, ∀ p, (1 + ‖p‖) ^ k * ‖ft (g : R3 → ℝ) p‖ ≤ C := by
  obtain ⟨C, hC⟩ := nf_schwartz_decay (nfFt g) k
  exact ⟨C, fun p => by rw [← nfFt_apply]; exact hC p⟩

/-! ### Integrability of `|p|^m |g_p| |p|^{-2}` -/

/-- `p ↦ |p|^{-2}` on the closed unit ball. -/
private def nfLoc (p : R3) : ℝ :=
  (Metric.closedBall (0 : R3) 1).indicator (fun p => (‖p‖ ^ 2)⁻¹) p

private lemma nfLoc_integrable : Integrable nfLoc := by
  have hloc : LocallyIntegrable (fun z : R3 => (‖z‖ ^ 2)⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 2) (by simp) (by simp; norm_num)
      (Eventually.of_forall fun z => ?_)
      (by fun_prop : Measurable fun z : R3 => (‖z‖ ^ 2)⁻¹).aestronglyMeasurable
    rw [Real.norm_of_nonneg (by positivity), one_mul, Real.rpow_neg (norm_nonneg _)]
    norm_cast
  exact (hloc.integrableOn_isCompact (isCompact_closedBall 0 1)).integrable_indicator
    Metric.isClosed_closedBall.measurableSet

private lemma nf_kerr_integrable : Integrable (fun p : R3 => ((1 + ‖p‖) ^ 4)⁻¹) := by
  have h : Integrable (fun z : R3 => (1 + ‖z‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  refine h.congr (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Real.rpow_neg (by positivity)]
  norm_cast

/-- `|p|^m |g_p| / |p|² ≤ M |p|^{-2} 1_{|p| ≤ 1} + C (1 + |p|)^{-4}`. -/
private lemma nf_weight_le (g : SchwartzMap R3 ℝ) (m : ℕ) :
    ∃ M C, ∀ p : R3, ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ / ‖p‖ ^ 2 ≤
      M * nfLoc p + C * ((1 + ‖p‖) ^ 4)⁻¹ := by
  obtain ⟨M, hM⟩ := nf_ft_decay g 0
  obtain ⟨C, hC⟩ := nf_ft_decay g (m + 4)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  refine ⟨M, C, fun p => ?_⟩
  have hM' : ‖ft (g : R3 → ℝ) p‖ ≤ M := by simpa using hM p
  by_cases hp : ‖p‖ ≤ 1
  · have hl : nfLoc p = (‖p‖ ^ 2)⁻¹ := by
      unfold nfLoc
      rw [Set.indicator_of_mem (by simpa using hp)]
    rw [hl, div_eq_mul_inv]
    have h1 : ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ ≤ M :=
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp)).trans hM'
    have h2 : 0 ≤ C * ((1 + ‖p‖) ^ 4)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (‖p‖ ^ 2)⁻¹)]
  · push Not at hp
    have hl : nfLoc p = 0 := by
      unfold nfLoc
      rw [Set.indicator_of_notMem (by simpa using hp.not_ge)]
    rw [hl, mul_zero, zero_add]
    have hp2 : 1 ≤ ‖p‖ ^ 2 := one_le_pow₀ hp.le
    have h1 : ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ / ‖p‖ ^ 2 ≤ ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ :=
      div_le_self (by positivity) hp2
    have h2 : ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ ≤ (1 + ‖p‖) ^ m * ‖ft (g : R3 → ℝ) p‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by linarith) m)
        (norm_nonneg _)
    have h3 : (1 + ‖p‖) ^ m * ‖ft (g : R3 → ℝ) p‖ ≤ C * ((1 + ‖p‖) ^ 4)⁻¹ := by
      have hq : 0 < (1 + ‖p‖) ^ 4 := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      calc (1 + ‖p‖) ^ m * ‖ft (g : R3 → ℝ) p‖ * (1 + ‖p‖) ^ 4
          = (1 + ‖p‖) ^ (m + 4) * ‖ft (g : R3 → ℝ) p‖ := by ring
        _ ≤ C := hC p
    linarith

/-- `p ↦ |p|^m |g_p| / |p|²` is integrable for every `m ∈ ℕ`. -/
private lemma nf_int_pow (g : SchwartzMap R3 ℝ) (m : ℕ) :
    Integrable (fun p : R3 => ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ / ‖p‖ ^ 2) := by
  obtain ⟨M, C, h⟩ := nf_weight_le g m
  refine ((nfLoc_integrable.const_mul M).add (nf_kerr_integrable.const_mul C)).mono' ?_
    (Eventually.of_forall fun p => ?_)
  · exact (((continuous_norm.pow m).mul (nf_ft_continuous g).norm).measurable.div
      (continuous_norm.pow 2).measurable).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact h p

/-! ### Subordination and the heat kernel -/

/-- The heat kernel `K_t(z) = (4πt)^{-3/2} e^{-|z|²/(4t)}`. -/
private def nfK (t : ℝ) (z : R3) : ℝ := (4 * π * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2 / (4 * t))

private lemma nfK_nonneg {t : ℝ} (ht : 0 < t) (z : R3) : 0 ≤ nfK t z := by
  unfold nfK
  positivity

private lemma nf_rpow_three_halves {a : ℝ} (ha : 0 < a) : a ^ (3 / 2 : ℝ) = a * √a := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- Subordination: `∫₀^∞ (4πt)^{-3/2} e^{-r²/(4t)} dt = (4πr)⁻¹` for `r > 0`. -/
private lemma nf_subord {r : ℝ} (hr : 0 < r) :
    ∫ t in Set.Ioi (0 : ℝ), (4 * π * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-r ^ 2 / (4 * t)) =
      (4 * π * r)⁻¹ := by
  set G : ℝ → ℝ := fun t => (4 * π * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-r ^ 2 / (4 * t)) with hG
  have hcv := integral_comp_rpow_Ioi G (p := -1) (by norm_num)
  rw [← hcv]
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • G (x ^ (-1 : ℝ)) =
      (4 * π) ^ (-(3 / 2 : ℝ)) * (x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(r ^ 2 / 4 * x))) := by
    intro x hx
    have hx0 : 0 < x := hx
    simp only [hG, smul_eq_mul, Real.rpow_neg_one, abs_neg, abs_one, one_mul]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hx0.le,
      Real.rpow_neg hx0.le, inv_inv]
    have he : -r ^ 2 / (4 * x⁻¹) = -(r ^ 2 / 4 * x) := by field_simp
    rw [he]
    have hx2 : x ^ ((-1 : ℝ) - 1) * x ^ (3 / 2 : ℝ) = x ^ ((1 / 2 : ℝ) - 1) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [← hx2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by positivity), Real.Gamma_one_half_eq]
  have h1 : (1 / (r ^ 2 / 4)) ^ (1 / 2 : ℝ) = 2 / r := by
    rw [show 1 / (r ^ 2 / 4) = (2 / r) ^ 2 by field_simp; ring, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (by positivity)]
  have h2 : (4 * π) ^ (-(3 / 2 : ℝ)) = (4 * π * (2 * √π))⁻¹ := by
    rw [Real.rpow_neg (by positivity), nf_rpow_three_halves (by positivity),
      Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [h1, h2]
  have hs : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-- `t ↦ K_t(z)` is integrable on `(0, ∞)` with integral `(4π|z|)⁻¹`, for `z ≠ 0`. -/
private lemma nfK_integral {z : R3} (hz : z ≠ 0) :
    IntegrableOn (fun t => nfK t z) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), nfK t z = (4 * π * ‖z‖)⁻¹ := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h := nf_subord hr
  have heq : ∫ t in Set.Ioi (0 : ℝ), nfK t z = (4 * π * ‖z‖)⁻¹ := h
  refine ⟨Integrable.of_integral_ne_zero ?_, heq⟩
  rw [heq]
  positivity

/-- `∫₀^∞ e^{-|p|² t} dt = |p|^{-2}` for `p ≠ 0`. -/
private lemma nf_exp_integral {p : R3} (hp : p ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-‖p‖ ^ 2 * t)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-‖p‖ ^ 2 * t) = (‖p‖ ^ 2)⁻¹ := by
  have ha : -‖p‖ ^ 2 < 0 := by
    have := norm_pos_iff.2 hp
    nlinarith
  refine ⟨integrableOn_exp_mul_Ioi ha 0, ?_⟩
  rw [integral_exp_mul_Ioi ha 0, mul_zero, Real.exp_zero]
  field_simp

private lemma nf_gauss_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : R3 => Real.exp (-‖p‖ ^ 2 * t)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := R3) (b := (t : ℂ))
    (by simpa using ht) 0 0).norm
  refine h.congr (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [Complex.norm_exp]
  congr 1
  simp only [zero_mul, add_zero]
  rw [show ((‖p‖ : ℂ) ^ 2) = ((‖p‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- `∫ e^{i⟨p,z⟩} e^{-t|p|²} dp = (π/t)^{3/2} e^{-|z|²/(4t)}` for `t > 0`. -/
private lemma nf_gauss_ft {t : ℝ} (ht : 0 < t) (z : R3) :
    ∫ p : R3, Complex.exp (-(t : ℂ) * ‖p‖ ^ 2 + Complex.I * ((inner ℝ z p : ℝ) : ℂ)) =
      (((π / t) ^ (3 / 2 : ℝ) * Real.exp (-‖z‖ ^ 2 / (4 * t)) : ℝ) : ℂ) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := R3) (b := (t : ℂ))
    (by simpa using ht) Complex.I z
  rw [h, finrank_euclideanSpace_fin, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity),
    Complex.ofReal_exp]
  congr 1
  · push_cast
    norm_num
  · congr 1
    rw [Complex.I_sq]
    push_cast
    ring

/-- `(π/t)^{3/2} = (2π)³ (4πt)^{-3/2}`. -/
private lemma nf_const {t : ℝ} (ht : 0 < t) :
    (π / t) ^ (3 / 2 : ℝ) = (2 * π) ^ 3 * (4 * π * t) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), nf_rpow_three_halves (by positivity),
    nf_rpow_three_halves (by positivity), Real.sqrt_div' _ ht.le, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by norm_num),
    show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have ha := Real.sq_sqrt Real.pi_pos.le
  have ha0 : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hb0 : 0 < √t := Real.sqrt_pos.2 ht
  field_simp
  rw [ha]
  norm_num

private lemma nf_norm_exp_I (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I r

/-- Heat semigroup: `(2π)^{-3} ∫ e^{i⟨p,x⟩} g_p e^{-t|p|²} dp = ∫ g(y) K_t(x - y) dy` for
`t > 0`. -/
private lemma nf_heat (g : SchwartzMap R3 ℝ) {t : ℝ} (ht : 0 < t) (x : R3) :
    ∫ p : R3, Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * ft (g : R3 → ℝ) p *
        ((Real.exp (-‖p‖ ^ 2 * t) : ℝ) : ℂ) =
      (((2 * π) ^ 3 : ℝ) : ℂ) * ((∫ y, g y * nfK t (x - y) : ℝ) : ℂ) := by
  set F : R3 → R3 → ℂ := fun p y => Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) *
    (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (g y : ℂ)) *
      ((Real.exp (-‖p‖ ^ 2 * t) : ℝ) : ℂ) with hFdef
  have hF : ∀ p, Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * ft (g : R3 → ℝ) p *
      ((Real.exp (-‖p‖ ^ 2 * t) : ℝ) : ℂ) = ∫ y, F p y := by
    intro p
    simp only [hFdef]
    rw [integral_mul_const, integral_const_mul]
    rfl
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine ((nf_gauss_integrable ht).mul_prod g.integrable.abs).mono' ?_
      (Eventually.of_forall fun q => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hFdef, Function.uncurry_def]
      have := g.continuous
      fun_prop
    · obtain ⟨p, y⟩ := q
      simp only [hFdef, Function.uncurry_apply_pair]
      rw [norm_mul, norm_mul, norm_mul, nf_norm_exp_I, Complex.norm_exp, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, neg_zero, Real.exp_zero]
      ring_nf
      exact le_rfl
  simp_rw [hF]
  rw [integral_integral_swap hint]
  have hpt : ∀ y, ∫ p, F p y =
      ((((2 * π) ^ 3 : ℝ) * (g y * nfK t (x - y)) : ℝ) : ℂ) := by
    intro y
    have h1 : ∀ p, F p y = (g y : ℂ) *
        Complex.exp (-(t : ℂ) * ‖p‖ ^ 2 + Complex.I * ((inner ℝ (x - y) p : ℝ) : ℂ)) := by
      intro p
      simp only [hFdef]
      rw [Complex.ofReal_exp, mul_comm _ (g y : ℂ), mul_comm (g y : ℂ)]
      rw [show ∀ a b c d : ℂ, a * (b * c) * d = c * (a * b * d) by intros; ring,
        ← Complex.exp_add, ← Complex.exp_add]
      congr 2
      rw [inner_sub_left, real_inner_comm x p, real_inner_comm y p]
      push_cast
      ring
    simp_rw [h1]
    rw [integral_const_mul, nf_gauss_ft ht, nf_const ht]
    unfold nfK
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_const_mul]
  push_cast
  ring

/-- `∫₀^∞ ∫ g(y) K_t(x - y) dy dt = (G ∗ g)(x)`. -/
private lemma nf_newton_heat (g : SchwartzMap R3 ℝ) (x : R3) :
    ∫ t in Set.Ioi (0 : ℝ), ∫ y, g y * nfK t (x - y) = newton (g : R3 → ℝ) x := by
  obtain ⟨C, hC⟩ := nf_g_bound g
  set f : ℝ → R3 → ℝ := fun t y => g y * nfK t (x - y) with hfdef
  have hslice : ∀ y, y ≠ x → ∫ t in Set.Ioi (0 : ℝ), ‖f t y‖ = |g y| / (4 * π * ‖x - y‖) := by
    intro y hy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hy.symm
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => |g y| * nfK t (x - y))
      (fun t ht => by
        simp only [hfdef]
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (nfK_nonneg ht _)]),
      integral_const_mul, (nfK_integral hz).2, div_eq_mul_inv]
  have hmeas : AEStronglyMeasurable (Function.uncurry f) ((volume.restrict (Set.Ioi 0)).prod
      volume) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hfdef, nfK, Function.uncurry_def]
    have := g.continuous
    fun_prop
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Set.Ioi 0)).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume x] with y hy
      exact ((nfK_integral (sub_ne_zero.2 hy.symm)).1).const_mul (g y)
    · refine (newton_integrable (h := fun y => |g y|) (k := 4) (C := C) (by norm_num)
        g.continuous.abs (fun y => by rw [abs_abs]; exact hC y) x).congr ?_
      filter_upwards [Measure.ae_ne volume x] with y hy
      exact (hslice y hy).symm
  rw [integral_integral_swap hint, newton]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume x] with y hy
  simp only [hfdef]
  rw [integral_const_mul, (nfK_integral (sub_ne_zero.2 hy.symm)).2, div_eq_mul_inv]

/-- `∫ e^{i⟨p,x⟩} g_p |p|^{-2} dp = (2π)³ (G ∗ g)(x)`. -/
private lemma nf_fourier_repr (g : SchwartzMap R3 ℝ) (x : R3) :
    ∫ p : R3, Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) * ft (g : R3 → ℝ) p /
        ((‖p‖ ^ 2 : ℝ) : ℂ) =
      (((2 * π) ^ 3 : ℝ) : ℂ) * ((newton (g : R3 → ℝ) x : ℝ) : ℂ) := by
  have hcont := nf_ft_continuous g
  set H : R3 → ℝ → ℂ := fun p t => Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) *
    ft (g : R3 → ℝ) p * ((Real.exp (-‖p‖ ^ 2 * t) : ℝ) : ℂ) with hHdef
  have hnorm : ∀ p, p ≠ 0 → ∫ t in Set.Ioi (0 : ℝ), ‖H p t‖ =
      ‖p‖ ^ 0 * ‖ft (g : R3 → ℝ) p‖ / ‖p‖ ^ 2 := by
    intro p hp
    simp only [hHdef]
    simp_rw [norm_mul, nf_norm_exp_I, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [integral_const_mul, (nf_exp_integral hp).2, pow_zero, one_mul, div_eq_mul_inv]
  have hmeas : AEStronglyMeasurable (Function.uncurry H)
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hHdef, Function.uncurry_def]
    fun_prop
  have hint : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Set.Ioi 0))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume 0] with p hp
      simp only [hHdef, Function.uncurry_apply_pair]
      exact ((nf_exp_integral hp).1.ofReal (𝕜 := ℂ)).const_mul _
    · refine (nf_int_pow g 0).congr ?_
      filter_upwards [Measure.ae_ne volume 0] with p hp
      exact (hnorm p hp).symm
  have hstep1 : ∀ᵐ p ∂(volume : Measure R3),
      Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) * ft (g : R3 → ℝ) p / ((‖p‖ ^ 2 : ℝ) : ℂ) =
        ∫ t in Set.Ioi (0 : ℝ), H p t := by
    filter_upwards [Measure.ae_ne volume 0] with p hp
    simp only [hHdef]
    rw [integral_const_mul, integral_complex_ofReal, (nf_exp_integral hp).2, div_eq_mul_inv]
    push_cast
    rfl
  rw [integral_congr_ae hstep1, integral_integral_swap hint,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => nf_heat g ht x), integral_const_mul,
    integral_complex_ofReal, nf_newton_heat]

/-! ### The Fourier representation of `G ∗ g` -/

/-- For a Schwartz function `g`, with `g_p = ∫ e^{-ipx} g(x) dx` the Fourier transform of §2:
`p ↦ |g_p| |p|^{-2}` and `p ↦ |p|^m |g_p| |p|^{-2}` (`m ∈ ℕ`) are integrable on ℝ³, and
`(G ∗ g)(x) = (2π)^{-3} ∫ e^{i⟨p,x⟩} g_p |p|^{-2} dp`, the position-space form of
`g_p = p² w_p`, (3.13) [gp], for `w = G ∗ g`. The integrand is read as `0` at `p = 0`. -/
theorem newton_eq_fourier (g : SchwartzMap R3 ℝ) :
    Integrable (fun p : R3 => ‖ft (g : R3 → ℝ) p‖ / ‖p‖ ^ 2) ∧
    (∀ m : ℕ, Integrable (fun p : R3 => ‖p‖ ^ m * ‖ft (g : R3 → ℝ) p‖ / ‖p‖ ^ 2)) ∧
    ∀ x : R3, ((newton (g : R3 → ℝ) x : ℝ) : ℂ) =
      ((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
        ∫ p : R3, Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) * ft (g : R3 → ℝ) p /
          ((‖p‖ ^ 2 : ℝ) : ℂ) := by
  refine ⟨?_, nf_int_pow g, fun x => ?_⟩
  · simpa using nf_int_pow g 0
  · rw [nf_fourier_repr, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity),
      Complex.ofReal_one, one_mul]

/-! ### Smoothness of `G ∗ g` and `-Δ (G ∗ g) = g` -/

/-- `𝐞(-⟪v, -(2π)⁻¹ x⟫) = e^{i⟨v,x⟩}`. -/
private lemma nf_phase (v x : R3) :
    ((𝐞 (-⟪v, (-(2 * π)⁻¹ : ℝ) • x⟫) : Circle) : ℂ) =
      Complex.exp (Complex.I * ((⟪v, x⟫ : ℝ) : ℂ)) := by
  rw [Real.fourierChar_apply, inner_smul_right]
  congr 1
  push_cast
  field_simp

/-- `∫ e^{i⟨p,x⟩} φ(p) dp = 𝓕 φ (-(2π)⁻¹ x)`. -/
private lemma nf_integral_eq_fourier (φ : R3 → ℂ) (x : R3) :
    ∫ p : R3, Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) * φ p =
      𝓕 φ ((-(2 * π)⁻¹ : ℝ) • x) := by
  rw [Real.fourier_eq]
  congr 1
  funext p
  rw [Circle.smul_def, nf_phase, smul_eq_mul]

/-- Fourier inversion in the convention of §2: `(2π)^{-3} ∫ e^{i⟨p,x⟩} g_p dp = g(x)`. -/
private lemma nf_inversion (g : SchwartzMap R3 ℝ) (x : R3) :
    ∫ p : R3, Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) * ft (g : R3 → ℝ) p =
      (((2 * π) ^ 3 : ℝ) : ℂ) * (g x : ℂ) := by
  set gc : R3 → ℂ := fun y => (g y : ℂ) with hgc
  set h : R3 → ℂ := fun u => 𝐞 ⟪u, x⟫ • 𝓕 gc u with hh
  have h1 : ∀ p : R3, Complex.exp (Complex.I * ((⟪p, x⟫ : ℝ) : ℂ)) * ft (g : R3 → ℝ) p =
      h ((2 * π)⁻¹ • p) := by
    intro p
    rw [scat_ft_eq_fourier, hh]
    simp only
    rw [Circle.smul_def, Real.fourierChar_apply, inner_smul_left]
    congr 2
    simp only [RCLike.conj_to_real]
    push_cast
    field_simp
  simp_rw [h1]
  rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin]
  have hinv : ∫ u, h u = 𝓕⁻ (𝓕 gc) x := by rw [Real.fourierInv_eq]
  have hgcS : gc = ⇑(nfC g) := rfl
  have hfi : 𝓕⁻ (𝓕 gc) = gc := by
    rw [hgcS]
    exact Continuous.fourierInv_fourier_eq (nfC g).continuous (nfC g).integrable
      (𝓕 (nfC g)).integrable
  rw [hinv, hfi, hgc]
  simp only
  rw [Complex.real_smul]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity)]

/-- `φ(p) = g_p / |p|²`. -/
private def nfPhi (g : SchwartzMap R3 ℝ) (p : R3) : ℂ := ft (g : R3 → ℝ) p / ((‖p‖ ^ 2 : ℝ) : ℂ)

private lemma nfPhi_moment (g : SchwartzMap R3 ℝ) (n : ℕ) :
    Integrable (fun v : R3 => ‖v‖ ^ n * ‖nfPhi g v‖) := by
  refine (nf_int_pow g n).congr (Eventually.of_forall fun v => ?_)
  simp only [nfPhi]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_div_assoc]

private lemma nfPhi_meas (g : SchwartzMap R3 ℝ) : AEStronglyMeasurable (nfPhi g) := by
  have hc := nf_ft_continuous g
  refine Measurable.aestronglyMeasurable ?_
  unfold nfPhi
  exact hc.measurable.div (by fun_prop)

/-- `G ∗ g = (2π)^{-3} Re 𝓕 φ (-(2π)⁻¹ ·)`. -/
private lemma nf_newton_eq (g : SchwartzMap R3 ℝ) :
    newton (g : R3 → ℝ) = fun x => ((2 * π) ^ 3)⁻¹ * (𝓕 (nfPhi g) ((-(2 * π)⁻¹ : ℝ) • x)).re := by
  funext x
  have h := congrArg Complex.re ((newton_eq_fourier g).2.2 x)
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at h
  rw [h, ← nf_integral_eq_fourier]
  simp only [nfPhi, mul_div_assoc]

private lemma nf_contDiff_F (g : SchwartzMap R3 ℝ) : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (nfPhi g)) :=
  Real.contDiff_fourier (fun n _ => nfPhi_moment g n)

/-- Second derivative of `𝓕 φ` in the direction `u`, as an integral. -/
private lemma nf_D2 (g : SchwartzMap R3 ℝ) (w u : R3) :
    iteratedFDeriv ℝ 2 (𝓕 (nfPhi g)) w ![u, u] =
      ∫ v : R3, 𝐞 (-⟪v, w⟫) • ((-(2 * π * Complex.I)) ^ 2 *
        (((⟪v, u⟫ * ⟪v, u⟫ : ℝ)) : ℂ) * nfPhi g v) := by
  rw [Real.iteratedFDeriv_fourier (N := ⊤) (fun n _ => nfPhi_moment g n) (nfPhi_meas g)
    (by exact_mod_cast le_top),
    Real.fourier_continuousMultilinearMap_apply
      (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (nfPhi_moment g 2)
        (nfPhi_meas g)), Real.fourier_eq]
  congr 1
  funext v
  rw [VectorFourier.fourierPowSMulRight_apply]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
    Complex.real_smul]
  rw [innerSL_apply_apply]
  push_cast
  congr 1
  ring

private lemma nf_D2_integrable (g : SchwartzMap R3 ℝ) (w u : R3) :
    Integrable (fun v : R3 => 𝐞 (-⟪v, w⟫) • ((-(2 * π * Complex.I)) ^ 2 *
        (((⟪v, u⟫ * ⟪v, u⟫ : ℝ)) : ℂ) * nfPhi g v)) := by
  rw [Real.fourierIntegral_convergent_iff]
  have hm := nfPhi_meas g
  refine ((nfPhi_moment g 2).const_mul ((2 * π) ^ 2 * ‖u‖ ^ 2)).mono' ?_
    (Eventually.of_forall fun v => ?_)
  · exact ((by fun_prop : Continuous fun v : R3 => (-(2 * π * Complex.I)) ^ 2 *
      (((⟪v, u⟫ * ⟪v, u⟫ : ℝ)) : ℂ)).aestronglyMeasurable).mul hm
  · rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, norm_mul, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_ofNat, Real.norm_of_nonneg pi_pos.le,
      Real.norm_eq_abs, abs_mul]
    have h1 : |⟪v, u⟫| ≤ ‖v‖ * ‖u‖ := abs_real_inner_le_norm v u
    have h2 : |⟪v, u⟫| * |⟪v, u⟫| ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
      have := mul_le_mul h1 h1 (abs_nonneg _) (by positivity)
      nlinarith
    have h3 := norm_nonneg (nfPhi g v)
    calc (2 * π) ^ 2 * (|⟪v, u⟫| * |⟪v, u⟫|) * ‖nfPhi g v‖
        ≤ (2 * π) ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) * ‖nfPhi g v‖ := by gcongr
      _ = _ := by ring

/-- For a Schwartz function `g`, `-Δ (G ∗ g) = g`: `G` is the fundamental solution of `-Δ`. -/
theorem newton_laplacian_schwartz (g : SchwartzMap R3 ℝ) (x : R3) :
    Laplacian.laplacian (newton (g : R3 → ℝ)) x = -g x := by
  set a : ℝ := -(2 * π)⁻¹ with ha
  set c : ℝ := ((2 * π) ^ 3)⁻¹ with hc
  set F := 𝓕 (nfPhi g) with hFdef
  set A : R3 →L[ℝ] R3 := a • ContinuousLinearMap.id ℝ R3 with hA
  set L : ℂ →L[ℝ] ℝ := c • Complex.reCLM with hL
  have hF : ContDiff ℝ 2 F :=
    (nf_contDiff_F g).of_le (WithTop.coe_le_coe.2 le_top)
  have heq : newton (g : R3 → ℝ) = L ∘ (F ∘ A) := by
    rw [nf_newton_eq]
    funext y
    simp [hL, hA, hc, ha, hFdef]
  set b := stdOrthonormalBasis ℝ R3 with hb
  rw [heq, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hcomp : ∀ i, iteratedFDeriv ℝ 2 (L ∘ (F ∘ A)) x ![b i, b i] =
      L (iteratedFDeriv ℝ 2 F (A x) ![a • b i, a • b i]) := by
    intro i
    rw [L.iteratedFDeriv_comp_left (hF.comp A.contDiff).contDiffAt le_rfl,
      A.iteratedFDeriv_comp_right hF x le_rfl]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 2
    funext j
    fin_cases j <;> simp [hA]
  simp_rw [hcomp, ← map_sum]
  simp_rw [hFdef, nf_D2]
  rw [← integral_finsetSum _ (fun i _ => nf_D2_integrable g _ _)]
  have hpt : ∀ᵐ v ∂(volume : Measure R3), ∑ i, 𝐞 (-⟪v, A x⟫) • ((-(2 * π * Complex.I)) ^ 2 *
      (((⟪v, a • b i⟫ * ⟪v, a • b i⟫ : ℝ)) : ℂ) * nfPhi g v) =
      -(Complex.exp (Complex.I * ((⟪v, x⟫ : ℝ) : ℂ)) * ft (g : R3 → ℝ) v) := by
    filter_upwards [Measure.ae_ne volume 0] with v hv
    have hAx : A x = (-(2 * π)⁻¹ : ℝ) • x := by simp [hA, ha]
    have hs : ∑ i, ((⟪v, a • b i⟫ * ⟪v, a • b i⟫ : ℝ)) = a ^ 2 * ‖v‖ ^ 2 := by
      have := b.sum_inner_mul_inner v v
      simp only [inner_smul_right]
      rw [real_inner_self_eq_norm_sq] at this
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (b i) v]
      ring
    have hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have := norm_pos_iff.2 hv
      exact_mod_cast (by positivity : (0 : ℝ) < ‖v‖ ^ 2).ne'
    simp_rw [Circle.smul_def, smul_eq_mul]
    rw [hAx, nf_phase]
    have hsum : ∑ i, Complex.exp (Complex.I * ((⟪v, x⟫ : ℝ) : ℂ)) * ((-(2 * π * Complex.I)) ^ 2 *
        (((⟪v, a • b i⟫ * ⟪v, a • b i⟫ : ℝ)) : ℂ) * nfPhi g v) =
        (Complex.exp (Complex.I * ((⟪v, x⟫ : ℝ) : ℂ)) * (-(2 * π * Complex.I)) ^ 2 *
          nfPhi g v) * ∑ i, (((⟪v, a • b i⟫ * ⟪v, a • b i⟫ : ℝ)) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, ← Complex.ofReal_sum, hs]
    simp only [nfPhi]
    field_simp
    rw [ha]
    push_cast
    rw [Complex.I_sq]
    field_simp
  rw [integral_congr_ae hpt, integral_neg, nf_inversion]
  simp only [hL, FunLike.coe_smul, Pi.smul_apply, Complex.reCLM_apply, smul_eq_mul,
    Complex.neg_re, Complex.re_ofReal_mul, Complex.ofReal_re, hc]
  field_simp

end LHYUpper
