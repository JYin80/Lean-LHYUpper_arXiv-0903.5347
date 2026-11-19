import LHYUpper.Riemann.ClosedForms

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! # The densities satisfy the Riemann-sum hypotheses (H1)–(H2)

Proves that the occupation integrand of (5.35), the kinetic integrand of (6.3), the potential
integrand in the proof of (7.8) [u-uPL] and the tail integrands of (5.39) [temp6.35] satisfy the
singularity and decay hypotheses (H1)–(H2) of the Riemann-sum lemma (`SingDecay`), with `(a, b) =
(1, 4)` for the occupation integrand and `(2, 4)` for the kinetic and potential integrands, and one
constant for the tail integrands uniformly in `t ≥ 0`. The estimates go through the radial variable
`σ = |k|` and the function `h(k)` of (5.34) [defhk]. -/

/-- Two one-sided bounds give the bound with `min` of the two inverse powers. -/
private lemma min_form {m n : ℕ} (hmn : m ≤ n) {σ y C : ℝ} (hσ : 0 < σ)
    (h1 : σ ≤ 1 → y ≤ C / σ ^ m) (h2 : 1 ≤ σ → y ≤ C / σ ^ n) :
    y ≤ C * min (σ ^ (-(m : ℝ))) (σ ^ (-(n : ℝ))) := by
  rw [Real.rpow_neg hσ.le, Real.rpow_neg hσ.le, Real.rpow_natCast, Real.rpow_natCast]
  rcases le_total σ 1 with h | h
  · have : (σ ^ m)⁻¹ ≤ (σ ^ n)⁻¹ := by
      apply inv_anti₀ (pow_pos hσ n)
      exact pow_le_pow_of_le_one hσ.le h hmn
    rw [min_eq_left this, ← div_eq_mul_inv]
    exact h1 h
  · have : (σ ^ n)⁻¹ ≤ (σ ^ m)⁻¹ := by
      apply inv_anti₀ (pow_pos hσ m)
      exact pow_le_pow_right₀ h hmn
    rw [min_eq_right this, ← div_eq_mul_inv]
    exact h2 h

/-- Radial reduction of `(H1)`–`(H2)`. -/
private theorem singDecay_radial {m n : ℕ} (hmn : m + 1 ≤ n) {F : R3 → ℝ} {f f' : ℝ → ℝ}
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hF : ∀ p : R3, p ≠ 0 → F p = f ‖p‖)
    (hd : ∀ σ : ℝ, 0 < σ → HasDerivAt f (f' σ) σ)
    (hf₁ : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → |f σ| ≤ C₀ / σ ^ m)
    (hf₂ : ∀ σ : ℝ, 0 < σ → 1 ≤ σ → |f σ| ≤ C₀ / σ ^ n)
    (hf'₁ : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → |f' σ| ≤ C₁ / σ ^ (m + 1))
    (hf'₂ : ∀ σ : ℝ, 0 < σ → 1 ≤ σ → |f' σ| ≤ C₁ / σ ^ n) :
    SingDecay (m : ℝ) (n : ℝ) (C₀ + C₁ * 2 ^ n) F := by
  have hb : ∀ σ : ℝ, 0 < σ → |f σ| ≤ C₀ * min (σ ^ (-(m : ℝ))) (σ ^ (-(n : ℝ))) := fun σ hσ =>
    min_form (by omega) hσ (hf₁ σ hσ) (hf₂ σ hσ)
  have hb' : ∀ σ : ℝ, 0 < σ →
      |f' σ| ≤ C₁ * min (σ ^ (-(m : ℝ) - 1)) (σ ^ (-(n : ℝ))) := fun σ hσ => by
    have := min_form hmn hσ (hf'₁ σ hσ) (hf'₂ σ hσ)
    have e : -(m : ℝ) - 1 = -((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  have hmin0 : ∀ ρ : ℝ, 0 < ρ → 0 ≤ min (ρ ^ (-(m : ℝ) - 1)) (ρ ^ (-(n : ℝ))) :=
    fun ρ hρ => le_min (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg hρ.le _)
  have hmin1 : ∀ ρ : ℝ, 0 < ρ → 0 ≤ min (ρ ^ (-(m : ℝ))) (ρ ^ (-(n : ℝ))) :=
    fun ρ hρ => le_min (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg hρ.le _)
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  refine ⟨fun p hp => ?_, fun p q hp hpq => ?_⟩
  · rw [hF p hp]
    refine (hb _ (norm_pos_iff.2 hp)).trans ?_
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC₁ h2n])
      (hmin1 _ (norm_pos_iff.2 hp))
  · have hu : 0 < ‖p‖ := norm_pos_iff.2 hp
    have hv1 : ‖p‖ / 2 ≤ ‖q‖ := by
      have h1 : ‖p‖ - ‖q‖ ≤ ‖p - q‖ := norm_sub_norm_le p q
      rw [norm_sub_rev] at h1
      linarith
    have hv2 : ‖q‖ ≤ 3 * ‖p‖ / 2 := by
      have h1 : ‖q‖ - ‖p‖ ≤ ‖q - p‖ := norm_sub_norm_le q p
      linarith
    have hq : q ≠ 0 := norm_pos_iff.1 (by linarith)
    rw [hF p hp, hF q hq]
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hbd : ∀ σ ∈ Set.Icc (‖p‖ / 2) (3 * ‖p‖ / 2),
        ‖f' σ‖ ≤ C₁ * 2 ^ n * min (‖p‖ ^ (-(m : ℝ) - 1)) (‖p‖ ^ (-(n : ℝ))) := by
      intro σ hσ
      have hσ0 : 0 < σ := by linarith [hσ.1]
      rw [Real.norm_eq_abs]
      refine (hb' σ hσ0).trans ?_
      have h1 : σ ^ (-(m : ℝ) - 1) ≤ (‖p‖ / 2) ^ (-(m : ℝ) - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hσ.1 (by linarith)
      have h2 : σ ^ (-(n : ℝ)) ≤ (‖p‖ / 2) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hσ.1 (by linarith)
      have e1 : (‖p‖ / 2) ^ (-(m : ℝ) - 1) = 2 ^ ((m : ℝ) + 1) * ‖p‖ ^ (-(m : ℝ) - 1) := by
        rw [Real.div_rpow hu.le zero_le_two, show -(m : ℝ) - 1 = -((m : ℝ) + 1) by ring,
          Real.rpow_neg zero_le_two]
        field_simp
      have e2 : (‖p‖ / 2) ^ (-(n : ℝ)) = 2 ^ n * ‖p‖ ^ (-(n : ℝ)) := by
        rw [Real.div_rpow hu.le zero_le_two, Real.rpow_neg zero_le_two, Real.rpow_natCast]
        field_simp
      have h3 : (2 : ℝ) ^ ((m : ℝ) + 1) ≤ 2 ^ n := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hmn'
      have hA : 0 ≤ ‖p‖ ^ (-(m : ℝ) - 1) := Real.rpow_nonneg hu.le _
      have h4 : 2 ^ ((m : ℝ) + 1) * ‖p‖ ^ (-(m : ℝ) - 1) ≤ 2 ^ n * ‖p‖ ^ (-(m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right h3 hA
      rw [mul_assoc, mul_min_of_nonneg _ _ h2n]
      refine mul_le_mul_of_nonneg_left (min_le_min ?_ ?_) hC₁
      · rw [e1] at h1; exact h1.trans h4
      · rw [e2] at h2; exact h2
    have hmv := (convex_Icc (‖p‖ / 2) (3 * ‖p‖ / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (fun σ hσ => (hd σ (by linarith [hσ.1])).hasDerivWithinAt) hbd
      (x := ‖p‖) (y := ‖q‖) ⟨by linarith, by linarith⟩ ⟨hv1, hv2⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hnn : 0 ≤ ‖q - p‖ := norm_nonneg _
    have hmin := hmin0 ‖p‖ hu
    calc |f ‖q‖ - f ‖p‖| ≤ C₁ * 2 ^ n * min (‖p‖ ^ (-(m : ℝ) - 1)) (‖p‖ ^ (-(n : ℝ))) *
          |‖q‖ - ‖p‖| := hmv
      _ ≤ C₁ * 2 ^ n * min (‖p‖ ^ (-(m : ℝ) - 1)) (‖p‖ ^ (-(n : ℝ))) * ‖q - p‖ :=
          mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le q p) (by positivity)
      _ ≤ (C₀ + C₁ * 2 ^ n) * ‖q - p‖ * min (‖p‖ ^ (-(m : ℝ) - 1)) (‖p‖ ^ (-(n : ℝ))) := by
          have : 0 ≤ ‖q - p‖ * min (‖p‖ ^ (-(m : ℝ) - 1)) (‖p‖ ^ (-(n : ℝ))) := mul_nonneg hnn hmin
          nlinarith [mul_nonneg hC₀ this]



/-- `h(k)` of (5.34) [defhk] as a function of `σ = |k|`. -/
private def hh (g σ : ℝ) : ℝ := Real.sqrt (1 + 4 * g / σ ^ 2)

private lemma hh_gt_one {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) : 1 < hh g σ := by
  unfold hh
  rw [Real.lt_sqrt zero_le_one]
  have : 0 < 4 * g / σ ^ 2 := by positivity
  nlinarith

private lemma hh_rel {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    σ ^ 2 * (hh g σ ^ 2 - 1) = 4 * g := by
  unfold hh
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

private lemma hasDerivAt_hh {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    HasDerivAt (hh g) (-(4 * g) / (σ ^ 3 * hh g σ)) σ := by
  have h1 : HasDerivAt (fun σ : ℝ => 1 + 4 * g / σ ^ 2) (-(8 * g) / σ ^ 3) σ := by
    have := ((hasDerivAt_const σ (4 * g)).div (hasDerivAt_pow 2 σ)
      (pow_ne_zero 2 hσ.ne')).const_add 1
    convert this using 1
    field_simp
    ring
  have h2 : HasDerivAt (hh g) (-(8 * g) / σ ^ 3 / (2 * hh g σ)) σ := h1.sqrt (by positivity)
  have hy : 0 < hh g σ := lt_trans zero_lt_one (hh_gt_one hg hσ)
  convert h2 using 1
  field_simp
  ring



private lemma y_sub_one_le {g σ y : ℝ} (hσ : 0 < σ) (hy : 1 < y)
    (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) : y - 1 ≤ 2 * g / σ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_pos (pow_pos hσ 2) (sub_pos.2 hy)).le (sub_pos.2 hy).le]

private lemma y_le_small {g σ y : ℝ} (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) : y * σ ≤ 1 + 2 * g := by
  by_contra hcon
  have hcon := not_le.1 hcon
  have h1 : (σ * y) ^ 2 = σ ^ 2 + 4 * g := by nlinarith
  have h2 : σ ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- `4g ≤ (1 + 2g) σ y` for `σ ≤ 1`. -/
private lemma four_g_le {g σ y : ℝ} (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hy : 1 < y)
    (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) : 4 * g ≤ (1 + 2 * g) * (σ * y) := by
  have h1 := y_le_small hg hσ hσ1 hrel
  have h2 : 0 < σ * y := mul_pos hσ (lt_trans zero_lt_one hy)
  nlinarith

private lemma val_large {g σ y ψ A : ℝ} (hA : 0 ≤ A) (hσ : 0 < σ) (hy : 1 < y)
    (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) (h : |ψ| ≤ A * (y - 1) ^ 2) :
    |ψ| ≤ 4 * A * g ^ 2 / σ ^ 4 := by
  have h1 := y_sub_one_le hσ hy hrel
  have h2 : (y - 1) ^ 2 ≤ (2 * g / σ ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  refine h.trans ?_
  calc A * (y - 1) ^ 2 ≤ A * (2 * g / σ ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h2 hA
    _ = 4 * A * g ^ 2 / σ ^ 4 := by field_simp; ring

private lemma val_small {g σ y ψ A : ℝ} (hA : 0 ≤ A) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hy : 1 < y) (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) (h : |ψ| ≤ A * y ^ 2) :
    |ψ| ≤ A * (1 + 2 * g) ^ 2 / σ ^ 2 := by
  have h1 := y_le_small hg hσ hσ1 hrel
  have h2 : y ≤ (1 + 2 * g) / σ := by rw [le_div_iff₀ hσ]; exact h1
  have h3 : y ^ 2 ≤ ((1 + 2 * g) / σ) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  refine h.trans ?_
  calc A * y ^ 2 ≤ A * ((1 + 2 * g) / σ) ^ 2 := mul_le_mul_of_nonneg_left h3 hA
    _ = A * (1 + 2 * g) ^ 2 / σ ^ 2 := by field_simp

/-- The derivative bound at small `σ` when `|ψ'| ≤ c (y - 1)`. -/
private lemma dprod_small {g σ y ψ' c : ℝ} (hc : 0 ≤ c) (hg : 0 < g) (hσ : 0 < σ) (hy : 1 < y)
    (h : |ψ'| ≤ c * (y - 1)) : |ψ' * (-(4 * g) / (σ ^ 3 * y))| ≤ 4 * c * g / σ ^ 3 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have e : |-(4 * g) / (σ ^ 3 * y)| = 4 * g / (σ ^ 3 * y) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 4 * g),
      abs_of_pos (by positivity : 0 < σ ^ 3 * y)]
  rw [abs_mul, e]
  calc |ψ'| * (4 * g / (σ ^ 3 * y)) ≤ c * (y - 1) * (4 * g / (σ ^ 3 * y)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ ≤ c * y * (4 * g / (σ ^ 3 * y)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hc
    _ = 4 * c * g / σ ^ 3 := by field_simp

/-- The derivative bound at small `σ` when `|ψ'|` is bounded by a constant. -/
private lemma dprod_small_const {g σ y ψ' c : ℝ} (hc : 0 ≤ c) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hy : 1 < y) (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) (h : |ψ'| ≤ c) :
    |ψ' * (-(4 * g) / (σ ^ 3 * y))| ≤ c * (1 + 2 * g) / σ ^ 2 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have e : |-(4 * g) / (σ ^ 3 * y)| = 4 * g / (σ ^ 3 * y) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 4 * g),
      abs_of_pos (by positivity : 0 < σ ^ 3 * y)]
  have h1 := four_g_le hg hσ hσ1 hy hrel
  have h2 : 4 * g / (σ ^ 3 * y) ≤ (1 + 2 * g) / σ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < σ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 this.le]
  rw [abs_mul, e]
  calc |ψ'| * (4 * g / (σ ^ 3 * y)) ≤ c * ((1 + 2 * g) / σ ^ 2) :=
        mul_le_mul h h2 (by positivity) hc
    _ = c * (1 + 2 * g) / σ ^ 2 := by ring

/-- The derivative bound at large `σ` when `|ψ'| ≤ c (y - 1)`. -/
private lemma dprod_large {g σ y ψ' c : ℝ} (hc : 0 ≤ c) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : 1 ≤ σ)
    (hy : 1 < y) (hrel : σ ^ 2 * (y ^ 2 - 1) = 4 * g) (h : |ψ'| ≤ c * (y - 1)) :
    |ψ' * (-(4 * g) / (σ ^ 3 * y))| ≤ 8 * c * g ^ 2 / σ ^ 4 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have e : |-(4 * g) / (σ ^ 3 * y)| = 4 * g / (σ ^ 3 * y) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 4 * g),
      abs_of_pos (by positivity : 0 < σ ^ 3 * y)]
  have h1 := y_sub_one_le hσ hy hrel
  have h2 : 4 * g / (σ ^ 3 * y) ≤ 4 * g / σ ^ 3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_pos hσ 3]
  rw [abs_mul, e]
  calc |ψ'| * (4 * g / (σ ^ 3 * y)) ≤ c * (y - 1) * (4 * g / σ ^ 3) :=
        mul_le_mul h (by exact h2) (by positivity) (by nlinarith)
    _ ≤ c * (2 * g / σ ^ 2) * (4 * g / σ ^ 3) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hc
    _ = 8 * c * g ^ 2 / σ ^ 5 := by field_simp; ring
    _ ≤ 8 * c * g ^ 2 / σ ^ 4 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_right₀ hσ1 (by norm_num)


/-- `(y - 1)² / (4y)`, the occupation integrand as a function of `h`. -/
private def psi1 (y : ℝ) : ℝ := (y - 1) ^ 2 / (4 * y)

private def dpsi1 (y : ℝ) : ℝ := (y ^ 2 - 1) / (4 * y ^ 2)

private lemma hasDerivAt_psi1 {y : ℝ} (hy : y ≠ 0) : HasDerivAt psi1 (dpsi1 y) y := by
  have h1 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1)) y := by
    simpa using ((hasDerivAt_id y).sub_const 1).fun_pow 2
  have h2 : HasDerivAt (fun x : ℝ => 4 * x) 4 y := by
    simpa using (hasDerivAt_id y).const_mul 4
  have := h1.fun_div h2 (by simpa using hy)
  have h : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 / (4 * x)) (dpsi1 y) y := by
    convert this using 1
    unfold dpsi1
    field_simp
    ring
  exact h

private lemma hasDerivAt_psi1_comp {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    HasDerivAt (fun σ => psi1 (hh g σ)) (dpsi1 (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ))) σ :=
  (hasDerivAt_psi1 (lt_trans zero_lt_one (hh_gt_one hg hσ)).ne').comp σ (hasDerivAt_hh hg hσ)

private lemma psi1_nonneg {y : ℝ} (hy : 1 < y) : 0 ≤ psi1 y := by
  unfold psi1
  have : 0 < y := lt_trans zero_lt_one hy
  positivity

private lemma psi1_le_y {y : ℝ} (hy : 1 < y) : psi1 y ≤ y / 4 := by
  unfold psi1
  have : 0 < y := lt_trans zero_lt_one hy
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

private lemma psi1_le_sq {y : ℝ} (hy : 1 < y) : psi1 y ≤ (1 / 4) * (y - 1) ^ 2 := by
  unfold psi1
  have : 0 < y := lt_trans zero_lt_one hy
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (y - 1), mul_nonneg (sq_nonneg (y - 1)) (sub_nonneg.2 hy.le)]

private lemma dpsi1_nonneg {y : ℝ} (hy : 1 < y) : 0 ≤ dpsi1 y := by
  unfold dpsi1
  have : 0 < y := lt_trans zero_lt_one hy
  have : 0 ≤ y ^ 2 - 1 := by nlinarith
  positivity

private lemma dpsi1_le_quarter {y : ℝ} (hy : 1 < y) : dpsi1 y ≤ 1 / 4 := by
  unfold dpsi1
  have : 0 < y := lt_trans zero_lt_one hy
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private lemma dpsi1_le {y : ℝ} (hy : 1 < y) : |dpsi1 y| ≤ (1 / 2) * (y - 1) := by
  rw [abs_of_nonneg (dpsi1_nonneg hy)]
  unfold dpsi1
  have : 0 < y := lt_trans zero_lt_one hy
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hy.le) (sub_nonneg.2 hy.le),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hy.le) (sub_nonneg.2 hy.le)) this.le]

private lemma psi1_small {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    |psi1 (hh g σ)| ≤ (1 + 2 * g + g ^ 2) / σ ^ 1 := by
  have hy := hh_gt_one hg hσ
  have hrel := hh_rel hg hσ
  rw [abs_of_nonneg (psi1_nonneg hy), pow_one]
  refine (psi1_le_y hy).trans ?_
  have h1 := y_le_small hg hσ hσ1 hrel
  have : hh g σ ≤ (1 + 2 * g) / σ := by rw [le_div_iff₀ hσ]; exact h1
  calc hh g σ / 4 ≤ (1 + 2 * g) / σ / 4 := by linarith
    _ ≤ (1 + 2 * g + g ^ 2) / σ := by
      rw [div_div, div_le_div_iff₀ (by positivity) hσ]
      nlinarith [sq_nonneg g, hσ]

private lemma psi1_large {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    |psi1 (hh g σ)| ≤ (1 + 2 * g + g ^ 2) / σ ^ 4 := by
  have hy := hh_gt_one hg hσ
  have hrel := hh_rel hg hσ
  have := val_large (A := 1 / 4) (ψ := psi1 (hh g σ)) (by norm_num) hσ hy hrel
    (by rw [abs_of_nonneg (psi1_nonneg hy)]; exact psi1_le_sq hy)
  refine this.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < σ ^ 4 := by positivity
  nlinarith [sq_nonneg g, mul_pos this this]

/-- The occupation integrand of (5.35) satisfies (H1)–(H2) with `(a, b) = (1, 4)`. -/
theorem singDecay_occDensity {g : ℝ} (hg : 0 < g) : ∃ C, 0 ≤ C ∧ SingDecay 1 4 C (occDensity g) := by
  have hK : (0 : ℝ) ≤ 1 + 2 * g + g ^ 2 := by positivity
  have key := singDecay_radial (m := 1) (n := 4) (by norm_num) (F := occDensity g)
    (f := fun σ => psi1 (hh g σ))
    (f' := fun σ => dpsi1 (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ)))
    (C₀ := 1 + 2 * g + g ^ 2) (C₁ := 1 + 2 * g + 4 * g ^ 2) hK (by positivity)
    (fun p _ => rfl) (fun σ hσ => hasDerivAt_psi1_comp hg hσ)
    (fun σ hσ hσ1 => psi1_small hg hσ hσ1) (fun σ hσ _ => psi1_large hg hσ)
    (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_)
  · exact ⟨1 + 2 * g + g ^ 2 + (1 + 2 * g + 4 * g ^ 2) * 2 ^ 4, by positivity,
      by exact_mod_cast key⟩
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    refine (dprod_small_const (c := 1 / 4) (by norm_num) hg hσ hσ1 hy hrel
      (by rw [abs_of_nonneg (dpsi1_nonneg hy)]; exact dpsi1_le_quarter hy)).trans ?_
    change _ ≤ _ / σ ^ 2
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    refine (dprod_large (c := 1 / 2) (by norm_num) hg hσ hσ1 hy hrel (dpsi1_le hy)).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)

/-- `(y - 1) / (y (y + 1)) - (y² - 1) / 4`; the kinetic integrand divided by `g₀`, as a function
of `h`. -/
private def psi2 (y : ℝ) : ℝ := (y - 1) / (y * (y + 1)) - (y ^ 2 - 1) / 4

private def dpsi2 (y : ℝ) : ℝ :=
  -((y - 1) * (y ^ 4 + 3 * y ^ 3 + 4 * y ^ 2 + 6 * y + 2)) / (2 * y ^ 2 * (y + 1) ^ 2)

private lemma hasDerivAt_psi2 {y : ℝ} (hy : 0 < y) : HasDerivAt psi2 (dpsi2 y) y := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 y := (hasDerivAt_id y).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => x * (x + 1)) (1 * (y + 1) + y * 1) y :=
    (hasDerivAt_id y).fun_mul ((hasDerivAt_id y).add_const 1)
  have h3 : HasDerivAt (fun x : ℝ => (x ^ 2 - 1) / 4) (2 * y / 4) y := by
    simpa using (((hasDerivAt_id y).fun_pow 2).sub_const 1).div_const 4
  have := (h1.fun_div h2 (by positivity)).sub h3
  have h : HasDerivAt (fun x : ℝ => (x - 1) / (x * (x + 1)) - (x ^ 2 - 1) / 4) (dpsi2 y) y := by
    convert this using 1
    unfold dpsi2
    field_simp
    ring
  exact h

private lemma psi2_eq {y : ℝ} (hy : 0 < y) :
    psi2 y = -((y - 1) ^ 2 * (y ^ 2 + 3 * y + 4) / (4 * y * (y + 1))) := by
  unfold psi2
  field_simp
  ring

private lemma abs_psi2_le {y : ℝ} (hy : 1 < y) : |psi2 y| ≤ 2 * (y - 1) ^ 2 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  rw [psi2_eq hy0, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (y - 1)) (sub_nonneg.2 hy.le),
    mul_nonneg (sq_nonneg (y - 1)) hy0.le, sq_nonneg (y - 1),
    mul_nonneg (mul_nonneg (sq_nonneg (y - 1)) hy0.le) hy0.le]

private lemma abs_dpsi2_le {y : ℝ} (hy : 1 < y) : |dpsi2 y| ≤ 8 * (y - 1) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have h1 : 0 < y - 1 := sub_pos.2 hy
  unfold dpsi2
  rw [abs_div, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤
      (y - 1) * (y ^ 4 + 3 * y ^ 3 + 4 * y ^ 2 + 6 * y + 2)),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * y ^ 2 * (y + 1) ^ 2), div_le_iff₀ (by positivity)]
  have h2 : y ^ 4 + 3 * y ^ 3 + 4 * y ^ 2 + 6 * y + 2 ≤ 16 * y ^ 2 * (y + 1) ^ 2 := by
    have h3 : 1 ≤ y := hy.le
    have h4 : 1 ≤ y ^ 2 := one_le_pow₀ h3
    have h5 : y ≤ y ^ 2 := by nlinarith
    have h6 : y ^ 2 ≤ y ^ 3 := by nlinarith
    have h7 : y ^ 3 ≤ y ^ 4 := by nlinarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h1.le]

private lemma hasDerivAt_psi2_comp {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    HasDerivAt (fun σ => g * psi2 (hh g σ))
      (g * dpsi2 (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ))) σ := by
  have h := ((hasDerivAt_psi2 (lt_trans zero_lt_one (hh_gt_one hg hσ))).comp σ
    (hasDerivAt_hh hg hσ)).const_mul g
  rw [← mul_assoc] at h
  exact h

private lemma kinDensity_eq_psi2 {g : ℝ} (hg : 0 < g) {p : R3} (hp : p ≠ 0) :
    kinDensity g p = g * psi2 (hh g ‖p‖) := by
  have hσ : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hy := hh_gt_one hg hσ
  have hrel := hh_rel hg hσ
  have e : hk g p = hh g ‖p‖ := rfl
  unfold kinDensity psi2
  rw [e]
  generalize hh g ‖p‖ = y at *
  generalize ‖p‖ = σ at *
  have hg' : g = σ ^ 2 * (y ^ 2 - 1) / 4 := by linarith
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hy1 : y + 1 ≠ 0 := by positivity
  have hy2 : y - 1 ≠ 0 := (sub_pos.2 hy).ne'
  subst hg'
  field_simp
  ring

/-- The kinetic integrand of (6.3) satisfies (H1)–(H2) with `(a, b) = (2, 4)`. -/
theorem singDecay_kinDensity {g : ℝ} (hg : 0 < g) : ∃ C, 0 ≤ C ∧ SingDecay 2 4 C (kinDensity g) := by
  have key := singDecay_radial (m := 2) (n := 4) (by norm_num) (F := kinDensity g)
    (f := fun σ => g * psi2 (hh g σ))
    (f' := fun σ => g * dpsi2 (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ)))
    (C₀ := 2 * g * (1 + 2 * g) ^ 2 + 8 * g ^ 3) (C₁ := 32 * g ^ 2 + 64 * g ^ 3)
    (by positivity) (by positivity)
    (fun p hp => kinDensity_eq_psi2 hg hp) (fun σ hσ => hasDerivAt_psi2_comp hg hσ)
    (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_)
  · exact ⟨2 * g * (1 + 2 * g) ^ 2 + 8 * g ^ 3 + (32 * g ^ 2 + 64 * g ^ 3) * 2 ^ 4,
      by positivity, by exact_mod_cast key⟩
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    have h1 : |g * psi2 (hh g σ)| ≤ 2 * g * (hh g σ) ^ 2 := by
      rw [abs_mul, abs_of_pos hg]
      have := abs_psi2_le hy
      have h2 : (hh g σ - 1) ^ 2 ≤ hh g σ ^ 2 := by nlinarith
      nlinarith
    refine (val_small (by positivity) hg hσ hσ1 hy hrel h1).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [pow_pos hg 3]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    have h1 : |g * psi2 (hh g σ)| ≤ 2 * g * (hh g σ - 1) ^ 2 := by
      rw [abs_mul, abs_of_pos hg]
      have := abs_psi2_le hy
      nlinarith
    refine (val_large (by positivity) hσ hy hrel h1).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [pow_pos hg 3, pow_pos hg 2]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    have h1 : |g * dpsi2 (hh g σ)| ≤ 8 * g * (hh g σ - 1) := by
      rw [abs_mul, abs_of_pos hg]
      have := abs_dpsi2_le hy
      nlinarith
    refine (dprod_small (by positivity) hg hσ hy h1).trans ?_
    change _ ≤ _ / σ ^ 3
    exact div_le_div_of_nonneg_right (by nlinarith [pow_pos hg 3, pow_pos hg 2]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    have h1 : |g * dpsi2 (hh g σ)| ≤ 8 * g * (hh g σ - 1) := by
      rw [abs_mul, abs_of_pos hg]
      have := abs_dpsi2_le hy
      nlinarith
    refine (dprod_large (by positivity) hg hσ hσ1 hy hrel h1).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [pow_pos hg 3, pow_pos hg 2]) (by positivity)

/-- `(y² - 1)(y - 1) / (4y)`, the potential integrand as a function of `h`. -/
private def psi3 (y : ℝ) : ℝ := (y ^ 2 - 1) * (y - 1) / (4 * y)

private def dpsi3 (y : ℝ) : ℝ := (y - 1) * (2 * y ^ 2 + y + 1) / (4 * y ^ 2)

private lemma hasDerivAt_psi3 {y : ℝ} (hy : 0 < y) : HasDerivAt psi3 (dpsi3 y) y := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * y) y := by
    simpa using ((hasDerivAt_id y).fun_pow 2).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => x - 1) 1 y := (hasDerivAt_id y).sub_const 1
  have h3 : HasDerivAt (fun x : ℝ => 4 * x) 4 y := by
    simpa using (hasDerivAt_id y).const_mul 4
  have := (h1.fun_mul h2).fun_div h3 (by positivity)
  have h : HasDerivAt (fun x : ℝ => (x ^ 2 - 1) * (x - 1) / (4 * x)) (dpsi3 y) y := by
    convert this using 1
    unfold dpsi3
    field_simp
    ring
  exact h

private lemma hasDerivAt_psi3_comp {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    HasDerivAt (fun σ => psi3 (hh g σ)) (dpsi3 (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ))) σ :=
  (hasDerivAt_psi3 (lt_trans zero_lt_one (hh_gt_one hg hσ))).comp σ (hasDerivAt_hh hg hσ)

private lemma psi3_nonneg {y : ℝ} (hy : 1 < y) : 0 ≤ psi3 y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have : 0 ≤ y ^ 2 - 1 := by nlinarith
  unfold psi3
  have : 0 ≤ y - 1 := by linarith
  positivity

private lemma psi3_le_sq {y : ℝ} (hy : 1 < y) : psi3 y ≤ (1 / 2) * (y - 1) ^ 2 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  unfold psi3
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (y - 1)) (sub_nonneg.2 hy.le)]

private lemma psi3_le_y_sq {y : ℝ} (hy : 1 < y) : psi3 y ≤ (1 / 4) * y ^ 2 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  unfold psi3
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private lemma dpsi3_nonneg {y : ℝ} (hy : 1 < y) : 0 ≤ dpsi3 y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have : 0 ≤ y - 1 := by linarith
  unfold dpsi3
  positivity

private lemma dpsi3_le {y : ℝ} (hy : 1 < y) : |dpsi3 y| ≤ 1 * (y - 1) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  rw [abs_of_nonneg (dpsi3_nonneg hy)]
  unfold dpsi3
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hy.le) (sub_nonneg.2 hy.le),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hy.le) (sub_nonneg.2 hy.le)) hy0.le]

private lemma potDensity_eq_psi3 {g : ℝ} (hg : 0 < g) {p : R3} (hp : p ≠ 0) :
    potDensity g p = psi3 (hh g ‖p‖) := by
  have hσ : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hy := hh_gt_one hg hσ
  have hrel := hh_rel hg hσ
  have e : hk g p = hh g ‖p‖ := rfl
  unfold potDensity psi3
  rw [e]
  generalize hh g ‖p‖ = y at *
  generalize ‖p‖ = σ at *
  have hg' : g = σ ^ 2 * (y ^ 2 - 1) / 4 := by linarith
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  subst hg'
  field_simp

/-- The potential integrand in the proof of (7.8) [u-uPL] satisfies (H1)–(H2) with `(a, b) = (2, 4)`. -/
theorem singDecay_potDensity {g : ℝ} (hg : 0 < g) : ∃ C, 0 ≤ C ∧ SingDecay 2 4 C (potDensity g) := by
  have key := singDecay_radial (m := 2) (n := 4) (by norm_num) (F := potDensity g)
    (f := fun σ => psi3 (hh g σ))
    (f' := fun σ => dpsi3 (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ)))
    (C₀ := (1 + 2 * g) ^ 2 + 2 * g ^ 2) (C₁ := 4 * g + 8 * g ^ 2)
    (by positivity) (by positivity)
    (fun p hp => potDensity_eq_psi3 hg hp) (fun σ hσ => hasDerivAt_psi3_comp hg hσ)
    (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_)
  · exact ⟨(1 + 2 * g) ^ 2 + 2 * g ^ 2 + (4 * g + 8 * g ^ 2) * 2 ^ 4,
      by positivity, by exact_mod_cast key⟩
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    have h1 : |psi3 (hh g σ)| ≤ (1 / 4) * hh g σ ^ 2 := by
      rw [abs_of_nonneg (psi3_nonneg hy)]; exact psi3_le_y_sq hy
    refine (val_small (by norm_num) hg hσ hσ1 hy hrel h1).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    have h1 : |psi3 (hh g σ)| ≤ (1 / 2) * (hh g σ - 1) ^ 2 := by
      rw [abs_of_nonneg (psi3_nonneg hy)]; exact psi3_le_sq hy
    refine (val_large (by norm_num) hσ hy hrel h1).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)
  · have hy := hh_gt_one hg hσ
    refine (dprod_small (c := 1) (by norm_num) hg hσ hy (dpsi3_le hy)).trans ?_
    change _ ≤ _ / σ ^ 3
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    refine (dprod_large (c := 1) (by norm_num) hg hσ hσ1 hy hrel (dpsi3_le hy)).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)

private lemma t_rpow_le {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    t * r ^ t ≤ 1 / (1 - r) := by
  have hu : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  have h1 : 1 - r ≤ -Real.log r := by linarith [Real.log_le_sub_one_of_pos hr0]
  have h2 : r ^ t = Real.exp (-(t * -Real.log r)) := by
    rw [Real.rpow_def_of_pos hr0]; congr 1; ring
  have h3 : t * -Real.log r ≤ Real.exp (t * -Real.log r) := by
    linarith [Real.add_one_le_exp (t * -Real.log r)]
  have h4 : t * r ^ t = (t * -Real.log r) * Real.exp (-(t * -Real.log r)) / (-Real.log r) := by
    have hne : Real.log r ≠ 0 := by intro h; rw [h] at hu; simp at hu
    rw [h2]; field_simp
  calc t * r ^ t = (t * -Real.log r) * Real.exp (-(t * -Real.log r)) / (-Real.log r) := h4
    _ ≤ Real.exp (t * -Real.log r) * Real.exp (-(t * -Real.log r)) / (-Real.log r) := by
        gcongr
    _ = 1 / (-Real.log r) := by rw [← Real.exp_add]; simp
    _ ≤ 1 / (1 - r) := one_div_le_one_div_of_le (by linarith) h1

/-- `(y - 1) / (y + 1) = |r|` as a function of `h`. -/
private def rr (y : ℝ) : ℝ := (y - 1) / (y + 1)

private lemma rr_pos {y : ℝ} (hy : 1 < y) : 0 < rr y := by
  unfold rr
  have : 0 < y - 1 := sub_pos.2 hy
  positivity

private lemma rr_lt_one {y : ℝ} (hy : 1 < y) : rr y < 1 := by
  unfold rr
  have : 0 < y + 1 := by linarith
  rw [div_lt_one this]
  linarith

private lemma hasDerivAt_rr {y : ℝ} (hy : 1 < y) : HasDerivAt rr (2 / (y + 1) ^ 2) y := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 y := (hasDerivAt_id y).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => x + 1) 1 y := (hasDerivAt_id y).add_const 1
  have := h1.fun_div h2 (by linarith : y + 1 ≠ 0)
  have h : HasDerivAt (fun x : ℝ => (x - 1) / (x + 1)) (2 / (y + 1) ^ 2) y := by
    convert this using 1
    have : y + 1 ≠ 0 := by linarith
    field_simp
    ring
  exact h

/-- `d/dy [rr(y)^t * psi1(y)]`. -/
private def tdpsi (t y : ℝ) : ℝ :=
  2 / (y + 1) ^ 2 * t * rr y ^ (t - 1) * psi1 y + rr y ^ t * dpsi1 y

private lemma hasDerivAt_tpsi {t y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun y => rr y ^ t * psi1 y) (tdpsi t y) y := by
  have h1 := (hasDerivAt_rr hy).rpow_const (p := t) (Or.inl (rr_pos hy).ne')
  exact h1.fun_mul (hasDerivAt_psi1 (lt_trans zero_lt_one hy).ne')

private lemma tdpsi_nonneg {t y : ℝ} (hy : 1 < y) (ht : 0 ≤ t) : 0 ≤ tdpsi t y := by
  have hr := rr_pos hy
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  unfold tdpsi
  have := dpsi1_nonneg hy
  have := psi1_nonneg hy
  have : 0 < y + 1 := by linarith
  positivity

private lemma tdpsi_le {t y : ℝ} (hy : 1 < y) (ht : 0 ≤ t) :
    tdpsi t y ≤ (y - 1) / (4 * y) + dpsi1 y := by
  have hr0 := rr_pos hy
  have hr1 := rr_lt_one hy
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hy1 : 0 < y - 1 := sub_pos.2 hy
  have hy2 : 0 < y + 1 := by linarith
  have hR1 : rr y ^ t ≤ 1 := Real.rpow_le_one hr0.le hr1.le ht
  have hR0 : 0 ≤ rr y ^ t := Real.rpow_nonneg hr0.le _
  have hT := t_rpow_le (t := t) hr0 hr1
  have h1r : 1 - rr y = 2 / (y + 1) := by unfold rr; field_simp; ring
  rw [h1r] at hT
  have hT' : t * rr y ^ t ≤ (y + 1) / 2 := by
    refine hT.trans (le_of_eq ?_); field_simp
  have hA : 2 / (y + 1) ^ 2 * t * rr y ^ (t - 1) * psi1 y
      = (t * rr y ^ t) * ((y - 1) / (2 * y * (y + 1))) := by
    rw [Real.rpow_sub_one hr0.ne']
    unfold psi1 rr
    field_simp
    ring
  unfold tdpsi
  rw [hA]
  have h2 : (t * rr y ^ t) * ((y - 1) / (2 * y * (y + 1))) ≤ (y - 1) / (4 * y) := by
    calc (t * rr y ^ t) * ((y - 1) / (2 * y * (y + 1)))
        ≤ ((y + 1) / 2) * ((y - 1) / (2 * y * (y + 1))) :=
          mul_le_mul_of_nonneg_right hT' (by positivity)
      _ = (y - 1) / (4 * y) := by field_simp; ring
  have h3 : rr y ^ t * dpsi1 y ≤ dpsi1 y := by
    have := dpsi1_nonneg hy
    nlinarith
  linarith

private lemma abs_tdpsi_le_half {t y : ℝ} (hy : 1 < y) (ht : 0 ≤ t) : |tdpsi t y| ≤ 1 / 2 := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  rw [abs_of_nonneg (tdpsi_nonneg hy ht)]
  have h1 : (y - 1) / (4 * y) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith [tdpsi_le hy ht, dpsi1_le_quarter hy]

private lemma abs_tdpsi_le_sub {t y : ℝ} (hy : 1 < y) (ht : 0 ≤ t) :
    |tdpsi t y| ≤ (3 / 4) * (y - 1) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  rw [abs_of_nonneg (tdpsi_nonneg hy ht)]
  have h1 : (y - 1) / (4 * y) ≤ (1 / 4) * (y - 1) := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 := dpsi1_le hy
  rw [abs_of_nonneg (dpsi1_nonneg hy)] at h2
  linarith [tdpsi_le hy ht]

private lemma tailDensity_eq {g : ℝ} (hg : 0 < g) (t : ℝ) {p : R3} (hp : p ≠ 0) :
    tailDensity g t p = rr (hh g ‖p‖) ^ t * psi1 (hh g ‖p‖) := by
  have hσ : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hy := hh_gt_one hg hσ
  have e : hk g p = hh g ‖p‖ := rfl
  have h : |rk g p| = rr (hh g ‖p‖) := by
    unfold rk
    rw [e]
    have h1 : 0 < 1 + hh g ‖p‖ := by linarith
    rw [abs_div, abs_of_pos h1, abs_of_neg (by linarith)]
    unfold rr
    rw [neg_sub]
    congr 1
    ring
  unfold tailDensity
  rw [h]
  rfl

/-- The tail integrands `|r|^t (h − 1)²/(4h)` satisfy (H1)–(H2) with one constant for all `t ≥ 0`. -/
theorem singDecay_tailDensity {g : ℝ} (hg : 0 < g) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → SingDecay 1 4 C (tailDensity g t) := by
  refine ⟨1 + 2 * g + g ^ 2 + (1 + 2 * g + 6 * g ^ 2) * 2 ^ 4, by positivity, fun t ht => ?_⟩
  have key := singDecay_radial (m := 1) (n := 4) (by norm_num) (F := tailDensity g t)
    (f := fun σ => rr (hh g σ) ^ t * psi1 (hh g σ))
    (f' := fun σ => tdpsi t (hh g σ) * (-(4 * g) / (σ ^ 3 * hh g σ)))
    (C₀ := 1 + 2 * g + g ^ 2) (C₁ := 1 + 2 * g + 6 * g ^ 2) (by positivity) (by positivity)
    (fun p hp => tailDensity_eq hg t hp)
    (fun σ hσ => (hasDerivAt_tpsi (hh_gt_one hg hσ)).comp σ
      (hasDerivAt_hh hg hσ))
    (fun σ hσ hσ1 => ?_) (fun σ hσ _ => ?_) (fun σ hσ hσ1 => ?_) (fun σ hσ hσ1 => ?_)
  · exact_mod_cast key
  · have hy := hh_gt_one hg hσ
    have hR1 : rr (hh g σ) ^ t ≤ 1 :=
      Real.rpow_le_one (rr_pos hy).le (rr_lt_one hy).le ht
    have hR0 : 0 ≤ rr (hh g σ) ^ t := Real.rpow_nonneg (rr_pos hy).le _
    rw [abs_mul, abs_of_nonneg hR0]
    refine le_trans ?_ (psi1_small hg hσ hσ1)
    calc rr (hh g σ) ^ t * |psi1 (hh g σ)| ≤ 1 * |psi1 (hh g σ)| :=
          mul_le_mul_of_nonneg_right hR1 (abs_nonneg _)
      _ = |psi1 (hh g σ)| := one_mul _
  · have hy := hh_gt_one hg hσ
    have hR1 : rr (hh g σ) ^ t ≤ 1 :=
      Real.rpow_le_one (rr_pos hy).le (rr_lt_one hy).le ht
    have hR0 : 0 ≤ rr (hh g σ) ^ t := Real.rpow_nonneg (rr_pos hy).le _
    rw [abs_mul, abs_of_nonneg hR0]
    refine le_trans ?_ (psi1_large hg hσ)
    calc rr (hh g σ) ^ t * |psi1 (hh g σ)| ≤ 1 * |psi1 (hh g σ)| :=
          mul_le_mul_of_nonneg_right hR1 (abs_nonneg _)
      _ = |psi1 (hh g σ)| := one_mul _
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    refine (dprod_small_const (c := 1 / 2) (by norm_num) hg hσ hσ1 hy hrel
      (abs_tdpsi_le_half hy ht)).trans ?_
    change _ ≤ _ / σ ^ 2
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)
  · have hy := hh_gt_one hg hσ
    have hrel := hh_rel hg hσ
    refine (dprod_large (c := 3 / 4) (by norm_num) hg hσ hσ1 hy hrel
      (abs_tdpsi_le_sub hy ht)).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg g]) (by positivity)

end LHYUpper
