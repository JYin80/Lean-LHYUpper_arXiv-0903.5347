module

public import LHYUpper.Scattering.Decay
public import LHYUpper.Scattering.FourierBasic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # Momentum-space properties of `g_p`

For `g = V(1 - w)` ((3.12) [gdef]) with `V` as in Theorem 2.1 [mainthm] and `w` the zero-energy
scattering solution, `g` is a nonnegative even Schwartz function. This file records the
consequences for `g_p = ∫ e^{-ipx} g(x) dx`: `g_0 = g₀`, `g_p` is real and even, `|g_p| ≤ g₀`,
`p ↦ g_p` is Lipschitz and Schwartz, `g_p` and `∇_p g_p` decay faster than any power of `|p|`,
and `|∇g|² + |g|²` has a local majorant of order `(1 + |p|)^{-4}`. -/

section Helpers

/-- Phase factor `e^{-i⟨p,x⟩}`. -/
private def mgPh (p x : R3) : ℂ := Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ)))

private lemma mgPh_norm (p x : R3) : ‖mgPh p x‖ = 1 := by
  unfold mgPh
  rw [Complex.norm_exp]
  simp

private lemma mgPh_continuous (p : R3) : Continuous (fun x => mgPh p x) := by
  unfold mgPh
  fun_prop

private lemma mg_ft_eq_ph (W : R3 → ℝ) (p : R3) : ft W p = ∫ x, mgPh p x * (W x : ℂ) := rfl

/-- `\overline{W_p} = W_{-p}`. -/
private lemma mg_ft_conj (W : R3 → ℝ) (p : R3) : (starRingEnd ℂ) (ft W p) = ft W (-p) := by
  rw [mg_ft_eq_ph, mg_ft_eq_ph, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  unfold mgPh
  rw [map_mul, ← Complex.exp_conj]
  simp [inner_neg_left]

/-- `W_{-p} = W_p` for even `W`. -/
private lemma mg_ft_neg_of_even (W : R3 → ℝ) (hW : ∀ x, W (-x) = W x) (p : R3) :
    ft W (-p) = ft W p := by
  have h := integral_neg_eq_self (fun x : R3 => mgPh p x * (W x : ℂ)) volume
  rw [mg_ft_eq_ph, mg_ft_eq_ph, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hW x]
  unfold mgPh
  simp [inner_neg_left, inner_neg_right]

/-- `W_p` is real for even `W`. -/
private lemma mg_ft_real_of_even (W : R3 → ℝ) (hW : ∀ x, W (-x) = W x) (p : R3) :
    ft W p = (((ft W p).re : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (ft W p) = ft W p := by rw [mg_ft_conj, mg_ft_neg_of_even W hW]
  exact (Complex.conj_eq_iff_re.1 h).symm

/-- `‖W_p‖ ≤ ∫ W` for `W ≥ 0`. -/
private lemma mg_ft_norm_le (W : R3 → ℝ) (hW : ∀ x, 0 ≤ W x) (p : R3) :
    ‖ft W p‖ ≤ ∫ x, W x := by
  unfold ft
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul]
  have h := mgPh_norm p x
  unfold mgPh at h
  rw [h, one_mul, Complex.norm_real, Real.norm_of_nonneg (hW x)]

/-- `W_p - W_q` bounded by `‖p - q‖ ∫ ‖x‖ W` for integrable `W` with `‖x‖ W` integrable. -/
private lemma mg_ft_sub_le (W : R3 → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hW : Integrable W)
    (hW1 : Integrable (fun x => ‖x‖ * W x)) (p q : R3) :
    ‖ft W p - ft W q‖ ≤ (∫ x, ‖x‖ * W x) * ‖p - q‖ := by
  have hint : ∀ r : R3, Integrable (fun x => Complex.exp (-(Complex.I * ((inner ℝ r x : ℝ) : ℂ))) *
      (W x : ℂ)) := by
    intro r
    refine Integrable.bdd_mul (c := 1) hW.ofReal ?_ ?_
    · exact (mgPh_continuous r).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => (mgPh_norm r x).le)
  unfold ft
  rw [← integral_sub (hint p) (hint q)]
  have hb : Integrable (fun x => ‖p - q‖ * (‖x‖ * W x)) := hW1.const_mul _
  refine (norm_integral_le_of_norm_le hb ?_).trans (le_of_eq ?_)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW0 x)]
    have h1 : ‖Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) -
        Complex.exp (-(Complex.I * ((inner ℝ q x : ℝ) : ℂ)))‖ ≤ ‖p - q‖ * ‖x‖ := by
      have h2 : Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) -
          Complex.exp (-(Complex.I * ((inner ℝ q x : ℝ) : ℂ))) =
          Complex.exp (-(Complex.I * ((inner ℝ q x : ℝ) : ℂ))) *
            (Complex.exp (Complex.I * ((inner ℝ (q - p) x : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, ← Complex.exp_add, mul_one, inner_sub_left]
        push_cast
        congr 2
        ring
      rw [h2, norm_mul]
      have h3 : ‖Complex.exp (-(Complex.I * ((inner ℝ q x : ℝ) : ℂ)))‖ = 1 := mgPh_norm q x
      rw [h3, one_mul]
      refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_sub_rev]
    calc _ ≤ (‖p - q‖ * ‖x‖) * W x := by gcongr; exact hW0 x
      _ = _ := by ring
  · rw [integral_const_mul, mul_comm]

/-- A nonnegative Schwartz function is integrable, and so is `‖x‖ W`. -/
private lemma mg_integrable_of_schwartz {W : R3 → ℝ}
    (hW : ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = W)
    (hW0 : ∀ x, 0 ≤ W x) : Integrable W ∧ Integrable (fun x => ‖x‖ * W x) := by
  obtain ⟨S, rfl⟩ := hW
  refine ⟨S.integrable, ?_⟩
  have h := S.integrable_pow_mul (volume : Measure R3) 1
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [pow_one, Real.norm_of_nonneg (hW0 x)]

/-- The Fourier transform of a real Schwartz function is a complex Schwartz function. -/
private lemma mg_ft_schwartz {W : R3 → ℝ} (hW : ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = W) :
    ∃ S : SchwartzMap R3 ℂ, (S : R3 → ℂ) = ft W := by
  obtain ⟨S, rfl⟩ := hW
  let Sc : SchwartzMap R3 ℂ := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM S
  let F : SchwartzMap R3 ℂ := SchwartzMap.fourierTransformCLM ℂ Sc
  let g : R3 ≃L[ℝ] R3 :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity))
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ g F, ?_⟩
  funext p
  change 𝓕 (fun x => (S x : ℂ)) (g p) = ft S p
  rw [scat_ft_eq_fourier]
  rfl

/-- Decay of a complex Schwartz function: `(1 + ‖p‖)^k ‖S p‖` is bounded. -/
private lemma mg_decay_of_schwartz (S : SchwartzMap R3 ℂ) (k : ℕ) :
    ∃ C, ∀ p, (1 + ‖p‖) ^ k * ‖S p‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
    fun p => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl S p
  rwa [norm_iteratedFDeriv_zero] at h

/-- Decay of the derivative of a complex Schwartz function. -/
private lemma mg_fderiv_decay_of_schwartz (S : SchwartzMap R3 ℂ) (k : ℕ) :
    ∃ C, ∀ p, (1 + ‖p‖) ^ k * ‖fderiv ℝ S p‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 1)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
    fun p => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 1)) (k := k) (n := 1)
    le_rfl le_rfl S p
  rwa [norm_iteratedFDeriv_one] at h

end Helpers

section
variable {V w : R3 → ℝ}

/-- `g_0 = g₀ = 4πa` (§3, after (3.13) [gp]). -/
theorem scat_ft_g_zero : ft (gfun V w) 0 = (g0 V w : ℂ) := by
  rw [scat_ft_zero]
  rfl

/-- `g_p` is real. -/
theorem scat_ft_g_real (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, ft (gfun V w) p = (((ft (gfun V w) p).re : ℝ) : ℂ) :=
  fun p => mg_ft_real_of_even _ (scat_g_even hV hw) p

/-- `g_{-p} = g_p`. -/
theorem scat_ft_g_neg (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, ft (gfun V w) (-p) = ft (gfun V w) p :=
  fun p => mg_ft_neg_of_even _ (scat_g_even hV hw) p

/-- `|g_p| ≤ g₀`. -/
theorem scat_ft_g_norm_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, ‖ft (gfun V w) p‖ ≤ g0 V w :=
  fun p => mg_ft_norm_le _ (scat_g_nonneg hV hw) p

/-- `p ↦ g_p` is Lipschitz. -/
theorem scat_ft_g_lipschitz (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C, ∀ p q, ‖ft (gfun V w) p - ft (gfun V w) q‖ ≤ C * ‖p - q‖ := by
  obtain ⟨h0, h1⟩ := mg_integrable_of_schwartz (scat_g_schwartz hV hw) (scat_g_nonneg hV hw)
  exact ⟨∫ x, ‖x‖ * gfun V w x, fun p q => mg_ft_sub_le _ (scat_g_nonneg hV hw) h0 h1 p q⟩

/-- `p ↦ g_p` is a Schwartz function. -/
theorem scat_ft_g_schwartz (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ S : SchwartzMap R3 ℂ, (S : R3 → ℂ) = ft (gfun V w) :=
  mg_ft_schwartz (scat_g_schwartz hV hw)

/-- `g_p` decays faster than any power of `|p|`. -/
theorem scat_ft_g_decay (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (k : ℕ) :
    ∃ C, ∀ p, (1 + ‖p‖) ^ k * ‖ft (gfun V w) p‖ ≤ C := by
  obtain ⟨S, hS⟩ := scat_ft_g_schwartz hV hw
  obtain ⟨C, hC⟩ := mg_decay_of_schwartz S k
  exact ⟨C, fun p => by simpa [hS] using hC p⟩

/-- `∇_p g_p` decays faster than any power of `|p|`. -/
theorem scat_fderiv_ft_g_decay (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (k : ℕ) :
    ∃ C, ∀ p, (1 + ‖p‖) ^ k * ‖fderiv ℝ (ft (gfun V w)) p‖ ≤ C := by
  obtain ⟨S, hS⟩ := scat_ft_g_schwartz hV hw
  obtain ⟨C, hC⟩ := mg_fderiv_decay_of_schwartz S k
  refine ⟨C, fun p => ?_⟩
  have := hC p
  rwa [show (S : R3 → ℂ) = ft (gfun V w) from hS] at this

end

end LHYUpper
