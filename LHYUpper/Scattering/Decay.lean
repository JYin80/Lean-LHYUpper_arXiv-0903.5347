import LHYUpper.Scattering.Solution

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # Regularity and decay of the scattering solution

For a potential `V` satisfying the hypotheses of Theorem 2.1 [mainthm] and the zero-energy
scattering solution `w` of §2, the function `g = V(1 - w)` ((3.12) [gdef]) is a Schwartz function,
`w` is smooth, `w = G ∗ g` is the Newton potential of `g`, `w(x) = a/|x| + O(|x|⁻²)` with
`a = g₀/(4π)`, and the integrands `g`, `V w`, `V w²` and `|∇w|²` are integrable. -/

section Helpers
variable {V w : R3 → ℝ}

/-- A Schwartz function is bounded by `C (1 + |y|)^{-5}`. -/
private lemma decay_schwartz_bound (S : SchwartzMap R3 ℝ) :
    ∃ C, ∀ y, |S y| ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
  refine ⟨2 ^ 5 * (Finset.Iic ((5, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S, fun y => ?_⟩
  have h : (1 + ‖y‖) ^ 5 * |S y| ≤ 2 ^ 5 * (Finset.Iic ((5, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5, 0) : ℕ × ℕ))
      (k := 5) (n := 0) le_rfl le_rfl S y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  rw [Real.rpow_neg (by positivity), show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- `g = V(1 - w)` is continuous and bounded by `C (1 + |y|)^{-5}`. -/
private lemma decay_g_bound (S : SchwartzMap R3 ℝ) (hS : (S : R3 → ℝ) = gfun V w) :
    Continuous (gfun V w) ∧ ∃ C, ∀ y, |gfun V w y| ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
  rw [← hS]
  exact ⟨S.continuous, decay_schwartz_bound S⟩

end Helpers

section
variable {V w : R3 → ℝ}

/-- `g = V(1 − w)` is a Schwartz function. -/
theorem scat_g_schwartz (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = gfun V w := by
  rw [scat_eq_bornSol hV hw]
  exact scat_bornSol_g_schwartz hV

/-- The scattering solution is smooth. -/
theorem scat_w_contDiff (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ContDiff ℝ (⊤ : ℕ∞) w := by
  rw [scat_eq_bornSol hV hw]
  exact scat_bornSol_contDiff hV

/-- `w = G ∗ g`: the scattering solution is the Newton potential of `g = V(1 − w)`. -/
theorem scat_w_newton (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ x, w x = ∫ y, gfun V w y / (4 * π * ‖x - y‖) := by
  intro x
  obtain rfl := scat_eq_bornSol hV hw
  exact (bornSol_isBornSolution hV).2.2 x

/-- `|w(x)| ≤ C/|x|`. -/
theorem scat_w_decay (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C, ∀ x, ‖x‖ * |w x| ≤ C := by
  obtain ⟨S, hS⟩ := scat_g_schwartz hV hw
  obtain ⟨hc, C, hC⟩ := decay_g_bound S hS
  obtain ⟨C', hC'⟩ := newton_decay (k := 5) (by norm_num) hc hC
  have hC'0 : 0 ≤ C' := by
    have h0 := hC' 0
    simp only [norm_zero, add_zero, div_one] at h0
    exact (abs_nonneg _).trans h0
  refine ⟨C', fun x => ?_⟩
  have hn := norm_nonneg x
  have h1 : |w x| ≤ C' / (1 + ‖x‖) := by
    rw [scat_w_newton hV hw x]
    exact hC' x
  calc ‖x‖ * |w x| ≤ ‖x‖ * (C' / (1 + ‖x‖)) := mul_le_mul_of_nonneg_left h1 hn
    _ = C' * (‖x‖ / (1 + ‖x‖)) := by ring
    _ ≤ C' * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 (by linarith)) hC'0
    _ = C' := mul_one _

/-- `|∇w(x)| ≤ C/|x|²`. -/
theorem scat_fderiv_w_decay (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C, ∀ x, ‖x‖ ^ 2 * ‖fderiv ℝ w x‖ ≤ C := by
  obtain ⟨S, hS⟩ := scat_g_schwartz hV hw
  obtain ⟨hc, C, hC⟩ := decay_g_bound S hS
  obtain ⟨C', hC'⟩ := newton_fderiv_decay (k := 5) (by norm_num) hc hC
  have hweq : w = newton (gfun V w) := funext fun x => scat_w_newton hV hw x
  have hder : fderiv ℝ w = fderiv ℝ (newton (gfun V w)) := congrArg (fderiv ℝ) hweq
  have hC'0 : 0 ≤ C' := by
    have h0 := hC' 0
    simp only [norm_zero, add_zero, one_pow, div_one] at h0
    exact (norm_nonneg _).trans h0
  refine ⟨C', fun x => ?_⟩
  have hn := norm_nonneg x
  have h1 : ‖fderiv ℝ w x‖ ≤ C' / (1 + ‖x‖) ^ 2 := by
    rw [hder]
    exact hC' x
  calc ‖x‖ ^ 2 * ‖fderiv ℝ w x‖ ≤ ‖x‖ ^ 2 * (C' / (1 + ‖x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C' * (‖x‖ ^ 2 / (1 + ‖x‖) ^ 2) := by ring
    _ ≤ C' * 1 := by
        refine mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 ?_) hC'0
        nlinarith
    _ = C' := mul_one _

/-- Integrability of `g`, `Vw`, `Vw²` and `|∇w|²`. -/
theorem scat_integrable (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Integrable (gfun V w) ∧ Integrable (fun x => V x * w x) ∧
      Integrable (fun x => V x * w x ^ 2) ∧ Integrable (fun x => ‖fderiv ℝ w x‖ ^ 2) := by
  obtain ⟨S, hS⟩ := scat_g_schwartz hV hw
  obtain ⟨T, hT⟩ := hV.schwartz
  have hVi : Integrable V := by rw [← hT]; exact T.integrable
  have hVc : Continuous V := by rw [← hT]; exact T.continuous
  have hwd : ContDiff ℝ (⊤ : ℕ∞) w := scat_w_contDiff hV hw
  have hwc : Continuous w := hwd.continuous
  have hdc : Continuous (fderiv ℝ w) := hwd.continuous_fderiv (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hS]; exact S.integrable
  · refine hVi.mono' (hVc.mul hwc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hV.nonneg x) (hw.nonneg x))]
    nlinarith [hV.nonneg x, hw.lt_one x]
  · refine hVi.mono' (hVc.mul (hwc.pow 2)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have h0 := hw.nonneg x
    have h1 := hw.lt_one x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hV.nonneg x) (sq_nonneg _))]
    nlinarith [hV.nonneg x, mul_nonneg (hV.nonneg x) h0,
      mul_nonneg (hV.nonneg x) (sub_nonneg.2 h1.le)]
  · obtain ⟨hc, C, hC⟩ := decay_g_bound S hS
    obtain ⟨C', hC'⟩ := newton_fderiv_decay (k := 5) (by norm_num) hc hC
    have hweq : w = newton (gfun V w) := funext fun x => scat_w_newton hV hw x
    have hder : fderiv ℝ w = fderiv ℝ (newton (gfun V w)) := congrArg (fderiv ℝ) hweq
    have hint : Integrable (fun x : R3 => C' ^ 2 * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul _
    refine hint.mono' (hdc.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have h1 : ‖fderiv ℝ w x‖ ≤ C' / (1 + ‖x‖) ^ 2 := by
      rw [hder]
      exact hC' x
    have hp : 0 < (1 + ‖x‖) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.rpow_neg (by positivity), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← div_eq_mul_inv]
    calc ‖fderiv ℝ w x‖ ^ 2 ≤ (C' / (1 + ‖x‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C' ^ 2 / (1 + ‖x‖) ^ 4 := by
          rw [div_pow, ← pow_mul]

end

end LHYUpper
