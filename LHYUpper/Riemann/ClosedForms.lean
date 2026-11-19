import LHYUpper.Riemann.Radial

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! # Closed forms and radial integrals of the Riemann-sum densities

Rewrites the densities of §5–§7 in terms of `h(k) = √(1 + 4g₀|k|⁻²)` and `r(k)`: `λ_k` on `P_L`
(3.15) [lambda], `ρλ_u = r(ρ^{-1/2}u)` (5.34) [defhk], and the occupation, kinetic (6.3) and
potential integrands. Evaluates their radial integrals after the scaling `s = √g σ`: `(2π)^{-3} ∫ (h
- 1)²/(4h) = g₀^{3/2}/(3π²)`, the constant of (3.14) [defrho0] and (5.3), together with the kinetic
and potential integrals, and gives the uniform bound `K (1 + t)^{-2}` for the tail integrals `|r|^t
(h - 1)²/(4h)`. -/

/-- On `P_L`, `λ_k` is `lamPL g₀ ρ k`, (3.15) [lambda]. -/
theorem lam_of_inPL {V w : R3 → ℝ} {ρ L : ℝ} {n : Idx} (h : inPL ρ L n) :
    lam V w ρ L n = lamPL (g0 V w) ρ (mom L n) := by
  simp [lam, lamPL, h]

/-- `ρλ_u = r(ρ^{-1/2}u)`, (5.34) [defhk]. -/
theorem rho_mul_lamPL {g ρ : ℝ} (hρ : 0 < ρ) (u : R3) :
    ρ * lamPL g ρ u = rk g ((ρ ^ (1/2 : ℝ))⁻¹ • u) := by
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hsq : (ρ ^ (1/2 : ℝ)) ^ 2 = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; norm_num
  have hn : ‖(ρ ^ (1/2 : ℝ))⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, mul_pow, inv_pow, hsq]; ring
  have he : 4 * g / ‖(ρ ^ (1/2 : ℝ))⁻¹ • u‖ ^ 2 = 4 * ρ * g / ‖u‖ ^ 2 := by
    rw [hn]
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    · field_simp
  simp only [rk, hk, lamPL, he]
  field_simp

private lemma hk_sq {g : ℝ} (hg : 0 ≤ g) {k : R3} (hk0 : k ≠ 0) :
    hk g k ^ 2 = 1 + 4 * (g / ‖k‖ ^ 2) := by
  have hn : 0 < ‖k‖ := norm_pos_iff.2 hk0
  unfold hk
  rw [Real.sq_sqrt (by positivity)]
  ring

private lemma one_le_hk {g : ℝ} (hg : 0 ≤ g) (k : R3) : 1 ≤ hk g k := by
  unfold hk
  rw [Real.one_le_sqrt]
  have : 0 ≤ 4 * g / ‖k‖ ^ 2 := by positivity
  linarith

private lemma occ_alg {h : ℝ} (hh : 0 < h) :
    ((1 - h) / (1 + h)) ^ 2 / (1 - ((1 - h) / (1 + h)) ^ 2) = (h - 1) ^ 2 / (4 * h) := by
  have h1 : 1 + h ≠ 0 := by positivity
  have h2 : 1 - ((1 - h) / (1 + h)) ^ 2 = 4 * h / (1 + h) ^ 2 := by
    field_simp; ring
  rw [h2]
  field_simp
  ring

private lemma pot_alg {h a : ℝ} (hh : 0 < h) (hsq : h ^ 2 = 1 + 4 * a) :
    (1 - h) / (1 + h) / (1 - ((1 - h) / (1 + h)) ^ 2) + a = a * (1 - 1 / h) := by
  have h1 : 1 + h ≠ 0 := by positivity
  have h2 : 1 - ((1 - h) / (1 + h)) ^ 2 = 4 * h / (1 + h) ^ 2 := by
    field_simp; ring
  rw [h2]
  field_simp
  nlinarith [hsq]

private lemma kin_alg {h a : ℝ} (hh : 0 < h) (hsq : h ^ 2 = 1 + 4 * a) :
    (h - 1) ^ 2 / (4 * h) - a ^ 2 = (1 + 2 * a) / (2 * h) - (1 + 2 * a ^ 2) / 2 := by
  field_simp
  nlinarith [hsq]

/-- `r²/(1 − r²) = (h − 1)²/(4h)`. -/
theorem occDensity_eq {g : ℝ} (hg : 0 ≤ g) (k : R3) :
    rk g k ^ 2 / (1 - rk g k ^ 2) = occDensity g k := by
  have hh : 0 < hk g k := lt_of_lt_of_le one_pos (one_le_hk hg k)
  exact occ_alg hh

/-- The kinetic integrand of (6.3) in terms of `r`. -/
theorem kinDensity_eq {g : ℝ} (hg : 0 ≤ g) (k : R3) :
    ‖k‖ ^ 2 * (rk g k ^ 2 / (1 - rk g k ^ 2) - (g / ‖k‖ ^ 2) ^ 2) = kinDensity g k := by
  have hh : 0 < hk g k := lt_of_lt_of_le one_pos (one_le_hk hg k)
  by_cases hk0 : k = 0
  · subst hk0
    simp [kinDensity, hk]
  · have e := occ_alg hh
    have hs := hk_sq hg hk0
    have := kin_alg hh (a := g / ‖k‖ ^ 2) hs
    unfold kinDensity
    rw [show rk g k ^ 2 / (1 - rk g k ^ 2) = (hk g k - 1) ^ 2 / (4 * hk g k) from e, this]
    congr 2
    ring

/-- The potential integrand in the proof of (7.8) [u-uPL], in terms of `r`. -/
theorem potDensity_eq {g : ℝ} (hg : 0 ≤ g) (k : R3) :
    rk g k / (1 - rk g k ^ 2) + g / ‖k‖ ^ 2 = potDensity g k := by
  have hh : 0 < hk g k := lt_of_lt_of_le one_pos (one_le_hk hg k)
  by_cases hk0 : k = 0
  · subst hk0
    simp [potDensity, hk, rk]
  · have hs := hk_sq hg hk0
    exact pot_alg hh (a := g / ‖k‖ ^ 2) hs

/-- `√(σ² + 4)`, the radial variable of the scaled integrals. -/
private def qf (σ : ℝ) : ℝ := Real.sqrt (σ ^ 2 + 4)

private lemma qf_sq (σ : ℝ) : qf σ ^ 2 = σ ^ 2 + 4 := Real.sq_sqrt (by positivity)

private lemma qf_nonneg (σ : ℝ) : 0 ≤ qf σ := Real.sqrt_nonneg _

private lemma two_le_qf (σ : ℝ) : 2 ≤ qf σ := by
  have h1 := qf_sq σ
  have h2 := qf_nonneg σ
  nlinarith [sq_nonneg σ]

private lemma qf_pos (σ : ℝ) : 0 < qf σ := lt_of_lt_of_le two_pos (two_le_qf σ)

private lemma lt_qf (σ : ℝ) : σ < qf σ := by
  have h : |σ| < qf σ := abs_lt_of_sq_lt_sq (by rw [qf_sq]; linarith) (qf_nonneg σ)
  exact lt_of_le_of_lt (le_abs_self σ) h

/-- `e(σ) = √(σ² + 4) − σ`. -/
private def ef (σ : ℝ) : ℝ := qf σ - σ

private lemma ef_pos (σ : ℝ) : 0 < ef σ := sub_pos.2 (lt_qf σ)

private lemma ef_mul (σ : ℝ) : (qf σ + σ) * ef σ = 4 := by
  unfold ef
  nlinarith [qf_sq σ]

private lemma ef_le_two {σ : ℝ} (hσ : 0 ≤ σ) : ef σ ≤ 2 := by
  have h1 := ef_mul σ
  have h2 := two_le_qf σ
  have h3 := ef_pos σ
  nlinarith

private lemma tendsto_ef : Tendsto ef atTop (𝓝 0) := by
  have h : Tendsto (fun σ : ℝ => 4 / (qf σ + σ)) atTop (𝓝 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    refine tendsto_atTop_mono (fun σ => ?_) tendsto_id
    have := qf_nonneg σ
    simp only [id]
    linarith
  refine h.congr (fun σ => ?_)
  have h1 := ef_mul σ
  have h2 : qf σ + σ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    norm_num at h1
  field_simp
  linarith

private lemma qf_param (σ : ℝ) :
    ∃ e : ℝ, 0 < e ∧ σ = (4 - e ^ 2) / (2 * e) ∧ qf σ = (4 + e ^ 2) / (2 * e) ∧
      ef σ = e := by
  have h2 := ef_pos σ
  have h3 := qf_sq σ
  refine ⟨ef σ, h2, ?_, ?_, rfl⟩
  · unfold ef at *
    field_simp
    nlinarith
  · unfold ef at *
    field_simp
    nlinarith

private lemma hasDerivAt_qf (σ : ℝ) : HasDerivAt qf (σ / qf σ) σ := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + 4) (2 * σ) σ := by
    simpa using ((hasDerivAt_id σ).pow 2).add_const 4
  have h2 := h1.sqrt (by positivity)
  have h3 := qf_pos σ
  refine h2.congr_deriv ?_
  unfold qf at h3 ⊢
  field_simp

private lemma hasDerivAt_ef (σ : ℝ) : HasDerivAt ef (-(ef σ / qf σ)) σ := by
  have h := (hasDerivAt_qf σ).sub (hasDerivAt_id σ)
  have h3 := qf_pos σ
  refine h.congr_deriv ?_
  unfold ef
  field_simp
  ring

/-- The scaled occupation integrand `σ e² / (4 q)`. -/
private def wocc (σ : ℝ) : ℝ := σ * ef σ ^ 2 / (4 * qf σ)

/-- The scaled kinetic integrand. -/
private def wkin (σ : ℝ) : ℝ := -(ef σ / qf σ) * (ef σ ^ 4 / 32 - 3 * ef σ ^ 2 / 8 + 2)

/-- The scaled potential integrand `1 − σ / q`. -/
private def wpot (σ : ℝ) : ℝ := ef σ / qf σ

private def Focc (σ : ℝ) : ℝ := ef σ ^ 3 / 24 - ef σ / 2

private def Fkin (σ : ℝ) : ℝ := ef σ ^ 5 / 160 - ef σ ^ 3 / 8 + 2 * ef σ

private def Fpot (σ : ℝ) : ℝ := -ef σ

private lemma hasDerivAt_Focc (σ : ℝ) : HasDerivAt Focc (wocc σ) σ := by
  have h := (((hasDerivAt_ef σ).pow 3).div_const 24).sub ((hasDerivAt_ef σ).div_const 2)
  refine h.congr_deriv ?_
  obtain ⟨e, he, hσ, hq, hee⟩ := qf_param σ
  unfold wocc
  rw [hee, hq, hσ]
  field_simp
  ring

private lemma hasDerivAt_Fkin (σ : ℝ) : HasDerivAt Fkin (wkin σ) σ := by
  have h := ((((hasDerivAt_ef σ).pow 5).div_const 160).sub
    (((hasDerivAt_ef σ).pow 3).div_const 8)).add ((hasDerivAt_ef σ).const_mul 2)
  refine h.congr_deriv ?_
  unfold wkin
  have := qf_pos σ
  field_simp
  ring

private lemma hasDerivAt_Fpot (σ : ℝ) : HasDerivAt Fpot (wpot σ) σ := by
  have h := (hasDerivAt_ef σ).neg
  refine h.congr_deriv ?_
  unfold wpot
  ring

private lemma qf_zero : qf 0 = 2 := by
  unfold qf
  rw [show ((0 : ℝ) ^ 2 + 4) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

private lemma ef_zero : ef 0 = 2 := by
  unfold ef
  rw [qf_zero]
  norm_num

private lemma tendsto_Focc : Tendsto Focc atTop (𝓝 0) := by
  have hc : Continuous (fun e : ℝ => e ^ 3 / 24 - e / 2) := by fun_prop
  have h := (hc.tendsto 0).comp tendsto_ef
  have e : Focc = fun σ => ef σ ^ 3 / 24 - ef σ / 2 := rfl
  rw [e]
  simpa [Function.comp_def] using h

private lemma tendsto_Fkin : Tendsto Fkin atTop (𝓝 0) := by
  have hc : Continuous (fun e : ℝ => e ^ 5 / 160 - e ^ 3 / 8 + 2 * e) := by fun_prop
  have h := (hc.tendsto 0).comp tendsto_ef
  have e : Fkin = fun σ => ef σ ^ 5 / 160 - ef σ ^ 3 / 8 + 2 * ef σ := rfl
  rw [e]
  simpa [Function.comp_def] using h

private lemma tendsto_Fpot : Tendsto Fpot atTop (𝓝 0) := by
  have e : Fpot = fun σ => -ef σ := rfl
  rw [e]
  simpa using tendsto_ef.neg

private lemma wocc_spec :
    IntegrableOn wocc (Set.Ioi 0) ∧ ∫ σ in Set.Ioi (0 : ℝ), wocc σ = 2 / 3 := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt Focc (wocc x) x := fun x _ => hasDerivAt_Focc x
  have hn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ wocc x := fun x hx => by
    unfold wocc
    have := qf_pos x
    have := Set.mem_Ioi.1 hx
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn tendsto_Focc, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn tendsto_Focc]
  simp only [Focc, ef_zero]
  norm_num

private lemma wkin_nonpos (x : ℝ) : wkin x ≤ 0 := by
  unfold wkin
  have h1 := qf_pos x
  have h2 := ef_pos x
  have hP : 0 < ef x ^ 4 / 32 - 3 * ef x ^ 2 / 8 + 2 := by
    nlinarith [sq_nonneg (ef x ^ 2 - 6)]
  have : 0 ≤ ef x / qf x := by positivity
  nlinarith

private lemma wkin_spec :
    IntegrableOn wkin (Set.Ioi 0) ∧ ∫ σ in Set.Ioi (0 : ℝ), wkin σ = -(16 / 5) := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt Fkin (wkin x) x := fun x _ => hasDerivAt_Fkin x
  have hn : ∀ x ∈ Set.Ioi (0 : ℝ), wkin x ≤ 0 := fun x _ => wkin_nonpos x
  refine ⟨integrableOn_Ioi_deriv_of_nonpos' hd hn tendsto_Fkin, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonpos' hd hn tendsto_Fkin]
  simp only [Fkin, ef_zero]
  norm_num

private lemma wpot_spec :
    IntegrableOn wpot (Set.Ioi 0) ∧ ∫ σ in Set.Ioi (0 : ℝ), wpot σ = 2 := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt Fpot (wpot x) x := fun x _ => hasDerivAt_Fpot x
  have hn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ wpot x := fun x _ => by
    unfold wpot
    have := qf_pos x
    have := ef_pos x
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn tendsto_Fpot, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn tendsto_Fpot]
  simp only [Fpot, ef_zero]
  norm_num

/-- `h` as a function of the radius `s = |k|`. -/
private def hrad (g s : ℝ) : ℝ := Real.sqrt (1 + 4 * g / s ^ 2)

private def occRad (g s : ℝ) : ℝ := (hrad g s - 1) ^ 2 / (4 * hrad g s)

private def kinRad (g s : ℝ) : ℝ :=
  s ^ 2 * ((1 + 2 * g / s ^ 2) / (2 * hrad g s) - (1 + 2 * (g / s ^ 2) ^ 2) / 2)

private def potRad (g s : ℝ) : ℝ := g / s ^ 2 * (1 - 1 / hrad g s)

private def tailRad (g t s : ℝ) : ℝ :=
  |(1 - hrad g s) / (1 + hrad g s)| ^ t * occRad g s

private lemma hrad_scale {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    hrad g (Real.sqrt g * σ) = qf σ / σ := by
  unfold hrad qf
  rw [mul_pow, Real.sq_sqrt hg.le]
  rw [show 1 + 4 * g / (g * σ ^ 2) = (σ ^ 2 + 4) / σ ^ 2 by field_simp]
  rw [Real.sqrt_div (by positivity), Real.sqrt_sq hσ.le]

/-- Radial integrals on `ℝ³` after the scaling `s = √g σ`. -/
private lemma radial_reduce {g : ℝ} (hg : 0 < g) {f w : ℝ → ℝ} {c : ℝ}
    (hw : ∀ σ : ℝ, 0 < σ → (Real.sqrt g * σ) ^ 2 * f (Real.sqrt g * σ) = c * w σ)
    (hwi : IntegrableOn w (Set.Ioi 0)) :
    Integrable (fun k : R3 => f ‖k‖) ∧
      ∫ k : R3, f ‖k‖ = 4 * π * (Real.sqrt g * (c * ∫ σ in Set.Ioi (0 : ℝ), w σ)) := by
  have hb : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hcongr : ∀ σ ∈ Set.Ioi (0 : ℝ),
      (fun s : ℝ => s ^ 2 * f s) (Real.sqrt g * σ) = c * w σ := fun σ hσ => hw σ hσ
  have hI : IntegrableOn (fun s : ℝ => s ^ 2 * f s) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun σ : ℝ => (fun s : ℝ => s ^ 2 * f s) (Real.sqrt g * σ))
        (Set.Ioi 0) := by
      rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
      exact hwi.const_mul c
    have h2 := (integrableOn_Ioi_comp_mul_left_iff (fun s : ℝ => s ^ 2 * f s) 0 hb).1 h1
    simpa using h2
  refine ⟨?_, ?_⟩
  · rw [integrable_fun_norm_addHaar volume]
    simpa [finrank_euclideanSpace_fin] using hI
  · rw [integral_radial]
    congr 1
    have h3 := integral_comp_mul_left_Ioi (fun s : ℝ => s ^ 2 * f s) 0 hb
    rw [mul_zero, setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      smul_eq_mul] at h3
    have h4 : ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * f s =
        Real.sqrt g * (c * ∫ σ in Set.Ioi (0 : ℝ), w σ) := by
      rw [h3, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
    exact h4

private lemma occ_scale {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    (Real.sqrt g * σ) ^ 2 * occRad g (Real.sqrt g * σ) = g * wocc σ := by
  unfold occRad wocc ef
  rw [hrad_scale hg hσ, mul_pow, Real.sq_sqrt hg.le]
  have := qf_pos σ
  field_simp

private lemma kin_scale {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    (Real.sqrt g * σ) ^ 2 * kinRad g (Real.sqrt g * σ) = g ^ 2 * wkin σ := by
  unfold kinRad wkin ef
  rw [hrad_scale hg hσ, mul_pow, Real.sq_sqrt hg.le]
  have hq0 := qf_pos σ
  field_simp
  linear_combination (16 * qf σ ^ 3 - 80 * qf σ ^ 2 * σ + qf σ * (176 * σ ^ 2 - 128) -
    240 * σ ^ 3 + 256 * σ) * qf_sq σ

private lemma pot_scale {g σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    (Real.sqrt g * σ) ^ 2 * potRad g (Real.sqrt g * σ) = g * wpot σ := by
  unfold potRad wpot ef
  rw [hrad_scale hg hσ, mul_pow, Real.sq_sqrt hg.le]
  have := qf_pos σ
  field_simp

/-- `|r|` in the scaled variable: `|r| = e²/4`. -/
private lemma abs_r_scale {σ : ℝ} (hσ : 0 < σ) :
    |(1 - qf σ / σ) / (1 + qf σ / σ)| = ef σ ^ 2 / 4 := by
  have hq := qf_pos σ
  have hm := ef_mul σ
  have h1 : (1 - qf σ / σ) / (1 + qf σ / σ) = -(ef σ ^ 2 / 4) := by
    have : 1 + qf σ / σ ≠ 0 := by positivity
    rw [div_eq_iff this]
    unfold ef at hm ⊢
    field_simp
    nlinarith [qf_sq σ]
  rw [h1, abs_neg, abs_of_pos (by have := ef_pos σ; positivity)]

private lemma tail_scale {g t σ : ℝ} (hg : 0 < g) (hσ : 0 < σ) :
    (Real.sqrt g * σ) ^ 2 * tailRad g t (Real.sqrt g * σ) =
      g * ((ef σ ^ 2 / 4) ^ t * wocc σ) := by
  unfold tailRad
  have h1 : hrad g (Real.sqrt g * σ) = qf σ / σ := hrad_scale hg hσ
  rw [h1, abs_r_scale hσ, mul_left_comm, occ_scale hg hσ]
  ring

private lemma rpow_three_halves {g : ℝ} (hg : 0 < g) : g ^ (3 / 2 : ℝ) = g * Real.sqrt g := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hg, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

private lemma rpow_five_halves {g : ℝ} (hg : 0 < g) :
    g ^ (5 / 2 : ℝ) = g ^ 2 * Real.sqrt g := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hg, Real.rpow_two,
    ← Real.sqrt_eq_rpow]

/-- `(2π)^{-3} ∫ (h − 1)²/(4h) = g₀^{3/2}/(3π²)`, the constant of (3.14) [defrho0] and (5.3). -/
theorem integral_occDensity {g : ℝ} (hg : 0 ≤ g) :
    Integrable (occDensity g) ∧
    ((2 * π) ^ 3)⁻¹ * ∫ k, occDensity g k = g ^ (3/2 : ℝ) / (3 * π ^ 2) := by
  rcases hg.eq_or_lt with rfl | hg
  · have h0 : occDensity 0 = fun _ => 0 := by
      funext k
      simp [occDensity, hk]
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp [Real.zero_rpow]
  · obtain ⟨hw1, hw2⟩ := wocc_spec
    obtain ⟨hI, hv⟩ := radial_reduce hg (f := occRad g) (w := wocc) (c := g)
      (fun σ hσ => occ_scale hg hσ) hw1
    refine ⟨hI, ?_⟩
    rw [hw2] at hv
    have hv' : ∫ k, occDensity g k = 4 * π * (Real.sqrt g * (g * (2 / 3))) := hv
    rw [hv', rpow_three_halves hg]
    have : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

/-- `(2π)^{-3} ∫` of the kinetic integrand of (6.3) is `−8g₀^{5/2}/(5π²)`. -/
theorem integral_kinDensity {g : ℝ} (hg : 0 ≤ g) :
    Integrable (kinDensity g) ∧
    ((2 * π) ^ 3)⁻¹ * ∫ k, kinDensity g k = -(8 * g ^ (5/2 : ℝ) / (5 * π ^ 2)) := by
  rcases hg.eq_or_lt with rfl | hg
  · have h0 : kinDensity 0 = fun _ => 0 := by
      funext k
      simp [kinDensity, hk]
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp [Real.zero_rpow]
  · obtain ⟨hw1, hw2⟩ := wkin_spec
    obtain ⟨hI, hv⟩ := radial_reduce hg (f := kinRad g) (w := wkin) (c := g ^ 2)
      (fun σ hσ => kin_scale hg hσ) hw1
    refine ⟨hI, ?_⟩
    rw [hw2] at hv
    have hv' : ∫ k, kinDensity g k = 4 * π * (Real.sqrt g * (g ^ 2 * (-(16 / 5)))) := hv
    rw [hv', rpow_five_halves hg]
    have : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

/-- `(2π)^{-3} ∫ g₀k^{-2}(1 − h^{-1}) = g₀^{3/2}/π²`. -/
theorem integral_potDensity {g : ℝ} (hg : 0 ≤ g) :
    Integrable (potDensity g) ∧
    ((2 * π) ^ 3)⁻¹ * ∫ k, potDensity g k = g ^ (3/2 : ℝ) / π ^ 2 := by
  rcases hg.eq_or_lt with rfl | hg
  · have h0 : potDensity 0 = fun _ => 0 := by
      funext k
      simp [potDensity, hk]
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp [Real.zero_rpow]
  · obtain ⟨hw1, hw2⟩ := wpot_spec
    obtain ⟨hI, hv⟩ := radial_reduce hg (f := potRad g) (w := wpot) (c := g)
      (fun σ hσ => pot_scale hg hσ) hw1
    refine ⟨hI, ?_⟩
    rw [hw2] at hv
    have hv' : ∫ k, potDensity g k = 4 * π * (Real.sqrt g * (g * 2)) := hv
    rw [hv', rpow_three_halves hg]
    have : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

private lemma continuous_qf : Continuous qf := by
  unfold qf
  fun_prop

private lemma continuous_ef : Continuous ef := by
  unfold ef
  exact continuous_qf.sub continuous_id

private lemma continuous_wocc : Continuous wocc := by
  unfold wocc
  exact (continuous_id.mul (continuous_ef.pow 2)).div (continuous_const.mul continuous_qf)
    (fun x => by have := qf_pos x; positivity)

/-- The scaled tail integrand `(e²/4)^t · σ e² / (4 q)`, with `|r| = e²/4`. -/
private def wtail (t σ : ℝ) : ℝ := (ef σ ^ 2 / 4) ^ t * wocc σ

private lemma wocc_nonneg {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ wocc σ := by
  unfold wocc
  have := qf_pos σ
  positivity

private lemma rho_le_one {σ : ℝ} (hσ : 0 ≤ σ) : ef σ ^ 2 / 4 ≤ 1 := by
  have := ef_le_two hσ
  have := ef_pos σ
  nlinarith

private lemma wtail_nonneg {t σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ wtail t σ := by
  unfold wtail
  have := wocc_nonneg hσ
  have := ef_pos σ
  positivity

private lemma wtail_le_wocc {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 ≤ σ) :
    wtail t σ ≤ wocc σ := by
  unfold wtail
  have h1 : (ef σ ^ 2 / 4) ^ t ≤ 1 :=
    Real.rpow_le_one (by positivity) (rho_le_one hσ) ht
  have h2 := wocc_nonneg hσ
  nlinarith

private lemma continuous_wtail {t : ℝ} (ht : 0 ≤ t) : Continuous (wtail t) := by
  unfold wtail
  exact ((continuous_ef.pow 2).div_const 4 |>.rpow_const (fun _ => Or.inr ht)).mul continuous_wocc

private lemma wtail_integrable {t : ℝ} (ht : 0 ≤ t) : IntegrableOn (wtail t) (Set.Ioi 0) := by
  refine Integrable.mono' wocc_spec.1 (continuous_wtail ht).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun σ hσ => ?_
  have hσ' : 0 ≤ σ := (Set.mem_Ioi.1 hσ).le
  rw [Real.norm_eq_abs, abs_of_nonneg (wtail_nonneg hσ')]
  exact wtail_le_wocc ht hσ'

private lemma wocc_le {σ : ℝ} (hσ : 0 ≤ σ) : wocc σ ≤ σ / 2 * (ef σ ^ 2 / 4) := by
  unfold wocc
  have h1 := qf_pos σ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hσ (sq_nonneg (ef σ))) (sub_nonneg.2 (two_le_qf σ))]

private lemma rho_mul_le {σ : ℝ} (hσ : 0 ≤ σ) : ef σ ^ 2 / 4 * (1 + σ / 2) ^ 2 ≤ 1 := by
  have hm := ef_mul σ
  have h2 := two_le_qf σ
  have h3 := ef_pos σ
  have h4 : ef σ * (1 + σ / 2) ≤ 2 := by nlinarith
  have h5 : 0 ≤ ef σ * (1 + σ / 2) := by positivity
  nlinarith

/-- The majorant `(σ/2)(1 + σ/2)^{-(2t+2)}` of the scaled tail integrand. -/
private def Bt (t σ : ℝ) : ℝ := σ / 2 * (1 + σ / 2) ^ (-(2 * t + 2))

private lemma wtail_le_Bt {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 ≤ σ) :
    wtail t σ ≤ Bt t σ := by
  unfold wtail Bt
  have hu : 0 < 1 + σ / 2 := by positivity
  have hρ : 0 < ef σ ^ 2 / 4 := by have := ef_pos σ; positivity
  have h1 : ef σ ^ 2 / 4 ≤ (1 + σ / 2) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hu.le, Real.rpow_two, ← one_div, le_div_iff₀ (by positivity)]
    simpa using rho_mul_le hσ
  have h2 : (ef σ ^ 2 / 4) ^ (t + 1) ≤ ((1 + σ / 2) ^ (-2 : ℝ)) ^ (t + 1) :=
    Real.rpow_le_rpow hρ.le h1 (by linarith)
  rw [← Real.rpow_mul hu.le, show -2 * (t + 1) = -(2 * t + 2) by ring] at h2
  rw [Real.rpow_add_one hρ.ne'] at h2
  have h3 := wocc_le hσ
  have h4 : 0 ≤ (ef σ ^ 2 / 4) ^ t := by positivity
  calc (ef σ ^ 2 / 4) ^ t * wocc σ ≤ (ef σ ^ 2 / 4) ^ t * (σ / 2 * (ef σ ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left h3 h4
    _ = σ / 2 * ((ef σ ^ 2 / 4) ^ t * (ef σ ^ 2 / 4)) := by ring
    _ ≤ σ / 2 * (1 + σ / 2) ^ (-(2 * t + 2)) := mul_le_mul_of_nonneg_left h2 (by positivity)

private def Abt (t σ : ℝ) : ℝ :=
  -(1 / t) * (1 + σ / 2) ^ (-(2 * t)) + 2 / (2 * t + 1) * (1 + σ / 2) ^ (-(2 * t + 1))

private lemma hasDerivAt_Abt {t : ℝ} (ht : 0 < t) {σ : ℝ} (hσ : 0 ≤ σ) :
    HasDerivAt (Abt t) (Bt t σ) σ := by
  have hu : 0 < 1 + σ / 2 := by positivity
  have hb : HasDerivAt (fun x : ℝ => 1 + x / 2) (1 / 2) σ := by
    simpa using ((hasDerivAt_id σ).div_const 2).const_add 1
  have h1 := (hb.rpow_const (p := -(2 * t)) (Or.inl hu.ne')).const_mul (-(1 / t))
  have h2 := (hb.rpow_const (p := -(2 * t + 1)) (Or.inl hu.ne')).const_mul (2 / (2 * t + 1))
  refine (h1.add h2).congr_deriv ?_
  have e1 : (1 + σ / 2) ^ (-(2 * t) - 1) = (1 + σ / 2) ^ (-(2 * t + 1)) := by
    rw [show -(2 * t) - 1 = -(2 * t + 1) by ring]
  have e2 : (1 + σ / 2) ^ (-(2 * t + 1) - 1) = (1 + σ / 2) ^ (-(2 * t + 2)) := by
    rw [show -(2 * t + 1) - 1 = -(2 * t + 2) by ring]
  have e3 : (1 + σ / 2) ^ (-(2 * t + 1)) = (1 + σ / 2) ^ (-(2 * t + 2)) * (1 + σ / 2) := by
    rw [← Real.rpow_add_one hu.ne']
    ring_nf
  rw [e1, e2, e3]
  unfold Bt
  have : 2 * t + 1 ≠ 0 := by positivity
  field_simp
  ring

private lemma tendsto_Abt {t : ℝ} (ht : 0 < t) : Tendsto (Abt t) atTop (𝓝 0) := by
  have hl : Tendsto (fun σ : ℝ => 1 + σ / 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_div_const two_pos)
  have h1 : Tendsto (fun σ : ℝ => (1 + σ / 2) ^ (-(2 * t))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 2 * t)).comp hl
  have h2 : Tendsto (fun σ : ℝ => (1 + σ / 2) ^ (-(2 * t + 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 2 * t + 1)).comp hl
  have h := (h1.const_mul (-(1 / t))).add (h2.const_mul (2 / (2 * t + 1)))
  have h0 : -(1 / t) * 0 + 2 / (2 * t + 1) * 0 = (0 : ℝ) := by ring
  rw [h0] at h
  exact h

private lemma Bt_spec {t : ℝ} (ht : 0 < t) :
    IntegrableOn (Bt t) (Set.Ioi 0) ∧
      ∫ σ in Set.Ioi (0 : ℝ), Bt t σ = 1 / t - 2 / (2 * t + 1) := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (Abt t) (Bt t x) x := fun x hx =>
    hasDerivAt_Abt ht (Set.mem_Ici.1 hx)
  have hn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ Bt t x := fun x hx => by
    unfold Bt
    have : 0 < x := hx
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn (tendsto_Abt ht), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn (tendsto_Abt ht)]
  simp [Abt]
  ring

/-- `∫_0^∞ (scaled tail integrand) ≤ (8/3)(1 + t)^{-2}`, uniformly in `t ≥ 0`. -/
private lemma wtail_bound {t : ℝ} (ht : 0 ≤ t) :
    ∫ σ in Set.Ioi (0 : ℝ), wtail t σ ≤ 8 / 3 * (1 + t) ^ (-2 : ℝ) := by
  have hpos : 0 < (1 + t) ^ 2 := by positivity
  have hrp : (1 + t) ^ (-2 : ℝ) = ((1 + t) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two]
  rw [hrp]
  have hint := wtail_integrable ht
  rcases le_total t 1 with h1 | h1
  · have h2 : ∫ σ in Set.Ioi (0 : ℝ), wtail t σ ≤ ∫ σ in Set.Ioi (0 : ℝ), wocc σ :=
      setIntegral_mono_on hint wocc_spec.1 measurableSet_Ioi
        (fun σ hσ => wtail_le_wocc ht (Set.mem_Ioi.1 hσ).le)
    rw [wocc_spec.2] at h2
    have h3 : (1 + t) ^ 2 ≤ 4 := by nlinarith
    have h4 : (4 : ℝ)⁻¹ ≤ ((1 + t) ^ 2)⁻¹ := inv_anti₀ hpos h3
    linarith
  · have htp : 0 < t := by linarith
    obtain ⟨hB, hBv⟩ := Bt_spec htp
    have h2 : ∫ σ in Set.Ioi (0 : ℝ), wtail t σ ≤ ∫ σ in Set.Ioi (0 : ℝ), Bt t σ :=
      setIntegral_mono_on hint hB measurableSet_Ioi
        (fun σ hσ => wtail_le_Bt ht (Set.mem_Ioi.1 hσ).le)
    rw [hBv] at h2
    have h3 : 1 / t - 2 / (2 * t + 1) ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
      have e : 1 / t - 2 / (2 * t + 1) = 1 / (t * (2 * t + 1)) := by
        field_simp
        ring
      rw [e, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hpos]
      nlinarith
    have h4 : 0 ≤ ((1 + t) ^ 2)⁻¹ := by positivity
    linarith

/-- `(2π)^{-3} ∫ |r|^t (h − 1)²/(4h) ≤ K (1 + t)^{-2}`, uniformly in `t ≥ 0`. -/
theorem integral_tailDensity_le {g : ℝ} (hg : 0 < g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      Integrable (tailDensity g t) ∧
      ((2 * π) ^ 3)⁻¹ * ∫ k, tailDensity g t k ≤ K * (1 + t) ^ (-2 : ℝ) := by
  set C : ℝ := ((2 * π) ^ 3)⁻¹ * (4 * π * (Real.sqrt g * g)) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C * (8 / 3), by positivity, fun t ht => ?_⟩
  obtain ⟨hI, hv⟩ := radial_reduce hg (f := tailRad g t) (w := wtail t) (c := g)
    (fun σ hσ => tail_scale hg hσ) (wtail_integrable ht)
  refine ⟨hI, ?_⟩
  have hv' : ∫ k, tailDensity g t k =
      4 * π * (Real.sqrt g * (g * ∫ σ in Set.Ioi (0 : ℝ), wtail t σ)) := hv
  rw [hv']
  calc ((2 * π) ^ 3)⁻¹ *
        (4 * π * (Real.sqrt g * (g * ∫ σ in Set.Ioi (0 : ℝ), wtail t σ)))
      = C * ∫ σ in Set.Ioi (0 : ℝ), wtail t σ := by rw [hC]; ring
    _ ≤ C * (8 / 3 * (1 + t) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left (wtail_bound ht) hC0
    _ = C * (8 / 3) * (1 + t) ^ (-2 : ℝ) := by ring

end LHYUpper
