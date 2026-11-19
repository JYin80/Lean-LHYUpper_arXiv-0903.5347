import LHYUpper.Scattering.WMomentum

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # The scattering identities of §4

For a potential `V` satisfying the hypotheses of Theorem 2.1 [mainthm], its zero-energy scattering
solution `w`, `g = V(1 - w)` ((3.12) [gdef]) and `w_p = g_p / |p|²` ((3.13) [gp]), this file proves
the two identities (4.14) of §4,
`‖∇w‖₂² - ‖Vw‖₁ + ‖Vw²‖₁ = 0` and `V₀ - ‖Vw‖₁ = g₀`,
and the momentum-space forms
`‖∇w‖₂² = (2π)^{-3} ∫ |g_p|² |p|^{-2} dp`, `∫ g w = (2π)^{-3} ∫ g_p w_p dp`,
`‖Vw‖₁ = (2π)^{-3} ∫ V_p w_p dp` and `‖Vw²‖₁ = (2π)^{-6} ∫∫ V_{u-v} w_u w_v du dv`.
Since `V ≥ 0` and `0 ≤ w < 1`, the `L¹` norms are the integrals `∫ V w`, `∫ V w²`.
The identity `∫ |∇w|² = ∫ g w` is integration by parts against the cutoff `χ(x/R)`; the error
term is `O(R^{-1})` by `|w(x)| ≤ C/|x|` and `|∇w(x)| ≤ C/|x|²`. -/

section Helpers
variable {V w : R3 → ℝ}

/-- `x ↦ e^{-i p·x} W(x)` is integrable for integrable `W`. -/
private lemma ident_phase_integrable {W : R3 → ℝ} (hW : Integrable W) (p : R3) :
    Integrable (fun x => Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * (W x : ℂ)) := by
  refine Integrable.bdd_mul (c := 1) hW.ofReal ?_ ?_
  · exact (by fun_prop : Continuous fun x : R3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ)))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Complex.norm_exp]
    simp

/-- `Re W_p = ∫ W(x) cos(p·x) dx` for real integrable `W`. -/
private lemma ident_ft_re {W : R3 → ℝ} (hW : Integrable W) (p : R3) :
    (ft W p).re = ∫ x, W x * Real.cos ⟪p, x⟫ := by
  unfold ft
  have hre : (∫ x, Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * (W x : ℂ)).re =
      ∫ x, (Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * (W x : ℂ)).re :=
    (integral_re (ident_phase_integrable hW p)).symm
  rw [hre]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Complex.re_mul_ofReal]
  have : -(Complex.I * ((inner ℝ p x : ℝ) : ℂ)) = ((-(inner ℝ p x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg, mul_comm]

private lemma ident_V_integrable (hV : PotentialHyp V) : Integrable V := by
  obtain ⟨S, hS⟩ := hV.schwartz
  rw [← hS]
  exact S.integrable

private lemma ident_V_continuous (hV : PotentialHyp V) : Continuous V := by
  obtain ⟨S, hS⟩ := hV.schwartz
  rw [← hS]
  exact S.continuous

private lemma ident_w_continuous (hw : IsScatteringSolution V w) : Continuous w :=
  hw.smooth.continuous

private lemma ident_g_continuous (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Continuous (gfun V w) := by
  unfold gfun
  exact (ident_V_continuous hV).mul (continuous_const.sub (ident_w_continuous hw))

/-- `∫ W w = (2π)^{-3} ∫ Re W_p w_p dp` for continuous integrable `W`. -/
private lemma ident_pair {W : R3 → ℝ} (hWc : Continuous W) (hW : Integrable W)
    (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∫ x, W x * w x = (2 * π)⁻¹ ^ 3 * ∫ p, (ft W p).re * wmom V w p := by
  have hwi := scat_wmom_integrable hV hw
  set F : R3 → R3 → ℝ := fun x p => W x * (wmom V w p * Real.cos ⟪p, x⟫) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : R3 × R3 => W q.1) (volume.prod volume) :=
      hWc.aestronglyMeasurable.comp_fst
    have h2 : AEStronglyMeasurable (fun q : R3 × R3 => wmom V w q.2) (volume.prod volume) :=
      hwi.aestronglyMeasurable.comp_snd
    have h3 : Continuous fun q : R3 × R3 => Real.cos ⟪q.2, q.1⟫ := by fun_prop
    exact h1.mul (h2.mul h3.aestronglyMeasurable)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (hW.abs.mul_prod hwi.abs).mono' hmeas (Eventually.of_forall fun q => ?_)
    obtain ⟨x, p⟩ := q
    simp only [hF, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
    have hc : |Real.cos ⟪p, x⟫| ≤ 1 := Real.abs_cos_le_one _
    have h0 : 0 ≤ |W x| * |wmom V w p| := by positivity
    calc |W x| * (|wmom V w p| * |Real.cos ⟪p, x⟫|)
        = |W x| * |wmom V w p| * |Real.cos ⟪p, x⟫| := by ring
      _ ≤ |W x| * |wmom V w p| * 1 := mul_le_mul_of_nonneg_left hc h0
      _ = |W x| * |wmom V w p| := mul_one _
  have h1 : ∀ x, W x * w x = (2 * π)⁻¹ ^ 3 * ∫ p, F x p := by
    intro x
    rw [scat_w_inversion hV hw x, hF]
    dsimp only
    rw [integral_const_mul]
    ring
  simp_rw [h1]
  rw [integral_const_mul, integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  simp only [hF]
  rw [ident_ft_re hW p, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  ring

/-- `Re (Vw)_p = Re V_p - Re g_p`. -/
private lemma ident_ft_Vw_re (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (p : R3) :
    (ft (fun x => V x * w x) p).re = (ft V p).re - (ft (gfun V w) p).re := by
  have hVi := ident_V_integrable hV
  have hVw := (scat_integrable hV hw).2.1
  have hcos : Continuous fun x => Real.cos ⟪p, x⟫ := by fun_prop
  have hcb : ∀ᵐ x ∂(volume : Measure R3), ‖Real.cos ⟪p, x⟫‖ ≤ 1 :=
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  rw [ident_ft_re hVw, ident_ft_re hVi, ident_ft_re (scat_integrable hV hw).1,
    ← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    unfold gfun
    ring
  · exact hVi.mul_bdd (c := 1) hcos.aestronglyMeasurable hcb
  · exact (scat_integrable hV hw).1.mul_bdd (c := 1) hcos.aestronglyMeasurable hcb

/-! ### The cutoff `χ(x/R)` -/

/-- The fixed bump `χ`: smooth, `0 ≤ χ ≤ 1`, `χ = 1` on the closed unit ball, `χ = 0` outside
the ball of radius `2`. -/
private def identBump : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cutoff `χ_R(x) = χ(x/R)`. -/
private def identCut (R : ℝ) (x : R3) : ℝ := identBump (R⁻¹ • x)

/-- The standard orthonormal basis of ℝ³. -/
private abbrev identBasis : OrthonormalBasis (Fin 3) ℝ R3 := EuclideanSpace.basisFun (Fin 3) ℝ

private lemma identCut_contDiff (R : ℝ) : ContDiff ℝ 2 (identCut R) :=
  identBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

private lemma identCut_hasFDerivAt (R : ℝ) (x : R3) :
    HasFDerivAt (identCut R)
      ((fderiv ℝ identBump (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ R3)) x := by
  have h1 : HasFDerivAt (fun y : R3 => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ R3) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h2 : HasFDerivAt identBump (fderiv ℝ identBump (R⁻¹ • x)) (R⁻¹ • x) :=
    ((identBump.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  exact h2.comp x h1

private lemma identCut_fderiv (R : ℝ) (x : R3) :
    fderiv ℝ (identCut R) x =
      (fderiv ℝ identBump (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ R3) :=
  (identCut_hasFDerivAt R x).fderiv

private lemma identBump_fderiv_bound : ∃ K, ∀ y, ‖fderiv ℝ identBump y‖ ≤ K :=
  ((identBump.contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (identBump.hasCompactSupport.fderiv ℝ)

private lemma identBump_fderiv_eq_zero {y : R3} (hy : ‖y‖ < 1) :
    fderiv ℝ identBump y = 0 := by
  have h : (identBump : R3 → ℝ) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    have hb : Metric.ball (0 : R3) 1 ∈ 𝓝 y :=
      Metric.isOpen_ball.mem_nhds (by simpa using hy)
    filter_upwards [hb] with z hz
    exact identBump.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

private lemma identBump_fderiv_ne_zero {y : R3} (hy : fderiv ℝ identBump y ≠ 0) :
    1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 := by
  constructor
  · by_contra h
    exact hy (identBump_fderiv_eq_zero (not_le.1 h))
  · have hmem : y ∈ tsupport identBump := support_fderiv_subset ℝ (Function.mem_support.2 hy)
    rw [identBump.tsupport_eq] at hmem
    simpa [identBump] using hmem

private lemma identCut_mem {R : ℝ} (hR : 0 < R) {x : R3} (hx : fderiv ℝ (identCut R) x ≠ 0) :
    R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R := by
  have h0 : fderiv ℝ identBump (R⁻¹ • x) ≠ 0 := by
    intro h
    apply hx
    rw [identCut_fderiv, h, ContinuousLinearMap.zero_comp]
  obtain ⟨h1, h2⟩ := identBump_fderiv_ne_zero h0
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)] at h1 h2
  have e : R * (R⁻¹ * ‖x‖) = ‖x‖ := by field_simp
  constructor
  · nlinarith
  · nlinarith

private lemma identCut_fderiv_norm_le {R : ℝ} (hR : 0 < R) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ identBump y‖ ≤ K) (x : R3) :
    ‖fderiv ℝ (identCut R) x‖ ≤ K * R⁻¹ := by
  rw [identCut_fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖R⁻¹ • ContinuousLinearMap.id ℝ R3‖ ≤ R⁻¹ := by
    refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ R3)).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
    exact mul_le_of_le_one_right (inv_pos.2 hR).le ContinuousLinearMap.norm_id_le
  exact mul_le_mul (hK _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hK 0))

private lemma identCut_eq_one {R : ℝ} (hR : 0 < R) {x : R3} (hx : ‖x‖ ≤ R) :
    identCut R x = 1 := by
  unfold identCut
  refine identBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hR)]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  linarith

private lemma identCut_fderiv_eq_zero {R : ℝ} (hR : 0 < R) {x : R3} (hx : ‖x‖ < R) :
    fderiv ℝ (identCut R) x = 0 := by
  by_contra h
  linarith [(identCut_mem hR h).1]

private lemma identCut_nonneg (R : ℝ) (x : R3) : 0 ≤ identCut R x := identBump.nonneg

private lemma identCut_le_one (R : ℝ) (x : R3) : identCut R x ≤ 1 := identBump.le_one

private lemma identCut_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (identCut R) :=
  identBump.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

/-- `∑ᵢ φ(eᵢ)² = ‖φ‖²` for a linear functional `φ` on ℝ³. -/
private lemma ident_sum_sq (φ : R3 →L[ℝ] ℝ) : ∑ i, (φ (identBasis i)) ^ 2 = ‖φ‖ ^ 2 := by
  set y := (InnerProductSpace.toDual ℝ R3).symm φ with hy
  have hφ : ∀ v, φ v = ⟪y, v⟫ := fun v => InnerProductSpace.toDual_symm_apply.symm
  have hn : ‖φ‖ = ‖y‖ := by rw [hy, LinearIsometryEquiv.norm_map]
  rw [hn, ← real_inner_self_eq_norm_sq, ← identBasis.sum_inner_mul_inner y y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hφ, sq, real_inner_comm (identBasis i) y]

/-- `Δw = ∑ᵢ ∂ᵢ∂ᵢ w`. -/
private lemma ident_laplacian_sum (hw : IsScatteringSolution V w) (x : R3) :
    ∑ i, fderiv ℝ (fun y => fderiv ℝ w y (identBasis i)) x (identBasis i) =
      Laplacian.laplacian w x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ w) x :=
    ((hw.smooth.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w identBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- `-Δw = g`. -/
private lemma ident_laplacian_w (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (x : R3) :
    Laplacian.laplacian w x = -gfun V w x := by
  obtain ⟨S, hS⟩ := scat_g_schwartz hV hw
  have hwn : w = newton (S : R3 → ℝ) := by
    funext y
    rw [hS]
    exact scat_w_newton hV hw y
  have h := newton_laplacian_schwartz S x
  rw [← hwn, hS] at h
  exact h

/-- Integration by parts against `χ_R`:
`∫ χ_R |∇w|² + ∫ w ∇χ_R·∇w - ∫ χ_R g w = 0`. -/
private lemma ident_cutoff_integral (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    {R : ℝ} (hR : 0 < R) :
    ∫ x, (identCut R x * ‖fderiv ℝ w x‖ ^ 2 +
      w x * (∑ i, fderiv ℝ (identCut R) x (identBasis i) * fderiv ℝ w x (identBasis i)) -
      identCut R x * (gfun V w x * w x)) = 0 := by
  have hχ : ContDiff ℝ 2 (identCut R) := identCut_contDiff R
  have hw2 : ContDiff ℝ 2 w := hw.smooth
  have hDw : ContDiff ℝ 1 (fderiv ℝ w) := hw2.fderiv_right le_rfl
  set F : R3 → ℝ := fun x => identCut R x * w x with hFdef
  have hF : ContDiff ℝ 2 F := hχ.mul hw2
  have hG : ∀ i, ContDiff ℝ 1 (fun x => fderiv ℝ w x (identBasis i)) :=
    fun i => hDw.clm_apply contDiff_const
  have hFcs : HasCompactSupport F := (identCut_hasCompactSupport hR).mul_right
  have hFd : ∀ x, DifferentiableAt ℝ F x := fun x => (hF.differentiable (by norm_num)) x
  have hGd : ∀ i x, DifferentiableAt ℝ (fun x => fderiv ℝ w x (identBasis i)) x :=
    fun i x => (hG i).differentiable one_ne_zero x
  have hI1 : ∀ i, Integrable (fun x =>
      F x * fderiv ℝ (fun y => fderiv ℝ w y (identBasis i)) x (identBasis i)) :=
    fun i => (hF.continuous.mul (((hG i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport hFcs.mul_right
  have hI2 : ∀ i, Integrable (fun x =>
      fderiv ℝ F x (identBasis i) * fderiv ℝ w x (identBasis i)) :=
    fun i => (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hG i).continuous).integrable_of_hasCompactSupport
        ((hFcs.fderiv_apply ℝ (identBasis i)).mul_right)
  have hI3 : ∀ i, Integrable (fun x => F x * fderiv ℝ w x (identBasis i)) :=
    fun i => (hF.continuous.mul (hG i).continuous).integrable_of_hasCompactSupport
      hFcs.mul_right
  have hibp : ∀ i, (∫ x, (F x * fderiv ℝ (fun y => fderiv ℝ w y (identBasis i)) x
      (identBasis i) + fderiv ℝ F x (identBasis i) * fderiv ℝ w x (identBasis i))) = 0 := by
    intro i
    rw [integral_add (hI1 i) (hI2 i), integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (hI2 i) (hI1 i) (hI3 i) (fun x _ => hFd x) (fun x _ => hGd i x)]
    ring
  have hpt : ∀ x, (identCut R x * ‖fderiv ℝ w x‖ ^ 2 +
      w x * (∑ i, fderiv ℝ (identCut R) x (identBasis i) * fderiv ℝ w x (identBasis i)) -
      identCut R x * (gfun V w x * w x)) = ∑ i, (F x * fderiv ℝ (fun y =>
        fderiv ℝ w y (identBasis i)) x (identBasis i) +
          fderiv ℝ F x (identBasis i) * fderiv ℝ w x (identBasis i)) := by
    intro x
    have hχd : DifferentiableAt ℝ (identCut R) x := (hχ.differentiable (by norm_num)) x
    have hwd : DifferentiableAt ℝ w x := (hw2.differentiable (by norm_num)) x
    have hfd : fderiv ℝ F x = identCut R x • fderiv ℝ w x + w x • fderiv ℝ (identCut R) x :=
      fderiv_fun_mul hχd hwd
    have hL := ident_laplacian_sum hw x
    rw [ident_laplacian_w hV hw x] at hL
    have hs := ident_sum_sq (fderiv ℝ w x)
    rw [Fin.sum_univ_three] at hL hs
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have hfd' : ∀ v, fderiv ℝ F x v =
        identCut R x * fderiv ℝ w x v + w x * fderiv ℝ (identCut R) x v := by
      intro v
      rw [hfd]
      simp
    rw [hfd' (identBasis 0), hfd' (identBasis 1), hfd' (identBasis 2)]
    simp only [hFdef]
    rw [← hs]
    linear_combination (-(identCut R x * w x)) * hL
  have hsum := integral_finsetSum (μ := volume) (f := fun i x => F x * fderiv ℝ (fun y =>
    fderiv ℝ w y (identBasis i)) x (identBasis i) + fderiv ℝ F x (identBasis i) *
      fderiv ℝ w x (identBasis i)) Finset.univ (fun i _ => (hI1 i).add (hI2 i))
  rw [integral_congr_ae (Eventually.of_forall hpt), hsum]
  exact Finset.sum_eq_zero fun i _ => hibp i

/-- The cutoff error `w ∇χ_R·∇w` is bounded by `M (1 + |x|)^{-4}` uniformly in `R ≥ 1`. -/
private lemma ident_err_bound {R : ℝ} (hR : 1 ≤ R) {K C₁ C₂ : ℝ}
    (hK : ∀ y, ‖fderiv ℝ identBump y‖ ≤ K) (hK0 : 0 ≤ K)
    (hC₁ : ∀ x, ‖x‖ * |w x| ≤ C₁) (hC₂ : ∀ x, ‖x‖ ^ 2 * ‖fderiv ℝ w x‖ ≤ C₂)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) (x : R3) :
    |w x * ∑ i, fderiv ℝ (identCut R) x (identBasis i) * fderiv ℝ w x (identBasis i)| ≤
      96 * C₁ * K * C₂ * ((1 + ‖x‖) ^ 4)⁻¹ := by
  have hR0 : 0 < R := by linarith
  by_cases h0 : fderiv ℝ (identCut R) x = 0
  · simp only [h0, zero_apply, zero_mul, Finset.sum_const_zero, mul_zero,
      abs_zero]
    positivity
  obtain ⟨h1, h2⟩ := identCut_mem hR0 h0
  set a := ‖x‖ with ha
  have hx1 : 1 ≤ a := le_trans hR h1
  set A := ‖fderiv ℝ (identCut R) x‖ with hA
  set B := ‖fderiv ℝ w x‖ with hB
  have hAnn : 0 ≤ A := norm_nonneg _
  have hBnn : 0 ≤ B := norm_nonneg _
  have hterm : ∀ i, |fderiv ℝ (identCut R) x (identBasis i) * fderiv ℝ w x (identBasis i)| ≤
      A * B := by
    intro i
    have hb : ‖identBasis i‖ = 1 := identBasis.orthonormal.1 i
    rw [abs_mul]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) hAnn
    · have := (fderiv ℝ (identCut R) x).le_opNorm (identBasis i)
      rwa [hb, mul_one, Real.norm_eq_abs] at this
    · have := (fderiv ℝ w x).le_opNorm (identBasis i)
      rwa [hb, mul_one, Real.norm_eq_abs] at this
  have hsum : |∑ i, fderiv ℝ (identCut R) x (identBasis i) * fderiv ℝ w x (identBasis i)| ≤
      3 * (A * B) := by
    rw [Fin.sum_univ_three]
    have e0 := hterm 0
    have e1 := hterm 1
    have e2 := hterm 2
    calc _ ≤ |fderiv ℝ (identCut R) x (identBasis 0) * fderiv ℝ w x (identBasis 0)| +
          |fderiv ℝ (identCut R) x (identBasis 1) * fderiv ℝ w x (identBasis 1)| +
          |fderiv ℝ (identCut R) x (identBasis 2) * fderiv ℝ w x (identBasis 2)| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 3 * (A * B) := by linarith
  have hAK : a * A ≤ 2 * K := by
    have hA1 : A ≤ K * R⁻¹ := identCut_fderiv_norm_le hR0 hK x
    have e : 2 * R * (K * R⁻¹) = 2 * K := by field_simp
    calc a * A ≤ 2 * R * (K * R⁻¹) := mul_le_mul h2 hA1 hAnn (by positivity)
      _ = 2 * K := e
  have hw1 : a * |w x| ≤ C₁ := hC₁ x
  have hw2 : a ^ 2 * B ≤ C₂ := hC₂ x
  have hpow : (1 + a) ^ 4 ≤ 16 * a ^ 4 := by
    have : 1 + a ≤ 2 * a := by linarith
    calc (1 + a) ^ 4 ≤ (2 * a) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
      _ = 16 * a ^ 4 := by ring
  have hmain : (1 + a) ^ 4 *
      |w x * ∑ i, fderiv ℝ (identCut R) x (identBasis i) * fderiv ℝ w x (identBasis i)| ≤
      96 * C₁ * K * C₂ := by
    rw [abs_mul]
    have hw0 : 0 ≤ |w x| := abs_nonneg _
    calc (1 + a) ^ 4 * (|w x| * |∑ i, fderiv ℝ (identCut R) x (identBasis i) *
          fderiv ℝ w x (identBasis i)|)
        ≤ (16 * a ^ 4) * (|w x| * (3 * (A * B))) := by gcongr
      _ = 48 * ((a * |w x|) * (a * A) * (a ^ 2 * B)) := by ring
      _ ≤ 48 * (C₁ * (2 * K) * C₂) := by
          have hp1 : (a * |w x|) * (a * A) ≤ C₁ * (2 * K) :=
            mul_le_mul hw1 hAK (by positivity) hC₁0
          have hp2 : (a * |w x|) * (a * A) * (a ^ 2 * B) ≤ C₁ * (2 * K) * C₂ :=
            mul_le_mul hp1 hw2 (by positivity) (by positivity)
          linarith
      _ = 96 * C₁ * K * C₂ := by ring
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact hmain

/-- `∫ |∇w|² = ∫ g w`, by integration by parts against `χ(x/R)` and `R → ∞`. -/
private lemma ident_grad_sq (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∫ x, ‖fderiv ℝ w x‖ ^ 2 = ∫ x, gfun V w x * w x := by
  obtain ⟨C₁, hC₁⟩ := scat_w_decay hV hw
  obtain ⟨C₂, hC₂⟩ := scat_fderiv_w_decay hV hw
  obtain ⟨K, hK⟩ := identBump_fderiv_bound
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := le_trans (by positivity) (hC₂ 0)
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hD := (scat_integrable hV hw).2.2.2
  have hgw : Integrable (fun x => gfun V w x * w x) := by
    refine ((scat_integrable hV hw).2.1.sub (scat_integrable hV hw).2.2.1).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, gfun]
    ring
  have hker : Integrable (fun x : R3 => ((1 + ‖x‖) ^ 4)⁻¹) := by
    have h := integrable_one_add_norm (E := R3) (μ := volume) (r := 4) (by simp; norm_num)
    refine h.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  have hwc : Continuous w := ident_w_continuous hw
  have hDc : Continuous (fderiv ℝ w) := hw.smooth.continuous_fderiv (by norm_num)
  have hgc : Continuous (gfun V w) := ident_g_continuous hV hw
  set M : ℝ := 96 * C₁ * K * C₂ with hM
  set h : ℕ → R3 → ℝ := fun n x => identCut (n + 1) x * ‖fderiv ℝ w x‖ ^ 2 +
      w x * (∑ i, fderiv ℝ (identCut (n + 1)) x (identBasis i) *
        fderiv ℝ w x (identBasis i)) -
      identCut (n + 1) x * (gfun V w x * w x) with hh
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (h n) volume := by
    intro n
    have hχc : Continuous (identCut ((n : ℝ) + 1)) := (identCut_contDiff _).continuous
    have hχd : Continuous (fderiv ℝ (identCut ((n : ℝ) + 1))) :=
      (identCut_contDiff _).continuous_fderiv (by norm_num)
    refine Continuous.aestronglyMeasurable ?_
    simp only [hh]
    refine ((hχc.mul ((continuous_norm.comp hDc).pow 2)).add (hwc.mul ?_)).sub
      (hχc.mul (hgc.mul hwc))
    exact continuous_finsetSum _ fun i _ =>
      (hχd.clm_apply continuous_const).mul (hDc.clm_apply continuous_const)
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure R3), ‖h n x‖ ≤
      ‖fderiv ℝ w x‖ ^ 2 + M * ((1 + ‖x‖) ^ 4)⁻¹ + |gfun V w x * w x| := by
    intro n
    refine Eventually.of_forall fun x => ?_
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have he := ident_err_bound hR hK hK0 hC₁ hC₂ hC₁0 hC₂0 x
    have hχ0 := identCut_nonneg ((n : ℝ) + 1) x
    have hχ1 := identCut_le_one ((n : ℝ) + 1) x
    simp only [hh, Real.norm_eq_abs]
    have t1 : |identCut ((n : ℝ) + 1) x * ‖fderiv ℝ w x‖ ^ 2| ≤ ‖fderiv ℝ w x‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg hχ0, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (by positivity) hχ1
    have t3 : |identCut ((n : ℝ) + 1) x * (gfun V w x * w x)| ≤ |gfun V w x * w x| := by
      rw [abs_mul, abs_of_nonneg hχ0]
      exact mul_le_of_le_one_left (abs_nonneg _) hχ1
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add t1 ?_)) t3
    simpa [hM] using he
  have hlim : ∀ᵐ x ∂(volume : Measure R3), Tendsto (fun n => h n x) atTop
      (𝓝 (‖fderiv ℝ w x‖ ^ 2 - gfun V w x * w x)) := by
    refine Eventually.of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hn' : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hh, identCut_eq_one hR0 hn'.le, identCut_fderiv_eq_zero hR0 hn',
      zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
      one_mul]
  have hint : Integrable (fun x => ‖fderiv ℝ w x‖ ^ 2 + M * ((1 + ‖x‖) ^ 4)⁻¹ +
      |gfun V w x * w x|) :=
    (hD.add (hker.const_mul M)).add hgw.abs
  have hT := tendsto_integral_of_dominated_convergence _ hmeas hint hbound hlim
  have h0 : ∀ n : ℕ, ∫ x, h n x = 0 := fun n => ident_cutoff_integral hV hw (by positivity)
  simp_rw [h0] at hT
  have hz := tendsto_nhds_unique hT tendsto_const_nhds
  rw [integral_sub hD hgw] at hz
  linarith

end Helpers

section
variable {V w : R3 → ℝ}

/-- `V₀ − ‖Vw‖₁ = g₀` (end of §4). -/
theorem scat_I1 (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    (∫ x, V x) - ∫ x, V x * w x = g0 V w := by
  rw [← integral_sub (ident_V_integrable hV) (scat_integrable hV hw).2.1]
  unfold g0 gfun
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  ring

/-- `‖∇w‖₂² − ‖Vw‖₁ + ‖Vw²‖₁ = 0` (end of §4). -/
theorem scat_I2 (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    (∫ x, ‖fderiv ℝ w x‖ ^ 2) - (∫ x, V x * w x) + ∫ x, V x * w x ^ 2 = 0 := by
  have hVw := (scat_integrable hV hw).2.1
  have hVw2 := (scat_integrable hV hw).2.2.1
  have h : ∫ x, gfun V w x * w x = (∫ x, V x * w x) - ∫ x, V x * w x ^ 2 := by
    rw [← integral_sub hVw hVw2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    unfold gfun
    ring
  rw [ident_grad_sq hV hw, h]
  ring

/-- `‖∇w‖₂² = (2π)^{-3} ∫ |g_p|²/|p|² dp`. -/
theorem scat_grad_w_sq (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∫ x, ‖fderiv ℝ w x‖ ^ 2 = (2 * π)⁻¹ ^ 3 * ∫ p, ‖ft (gfun V w) p‖ ^ 2 / ‖p‖ ^ 2 := by
  rw [ident_grad_sq hV hw,
    ident_pair (ident_g_continuous hV hw) (scat_integrable hV hw).1 hV hw]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  have hn : ‖ft (gfun V w) p‖ = |(ft (gfun V w) p).re| := by
    rw [scat_ft_g_real hV hw p, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rw [hn, sq_abs, wmom, mul_div_assoc', sq]
  ring

/-- `‖Vw‖₁ = (2π)^{-3} ∫ V_p w_p dp`. -/
theorem scat_Vw_eq (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∫ x, V x * w x = (2 * π)⁻¹ ^ 3 * ∫ p, (ft V p).re * wmom V w p := by
  exact ident_pair (ident_V_continuous hV) (ident_V_integrable hV) hV hw

/-- `‖Vw²‖₁ = (2π)^{-6} ∫∫ V_{u−v} w_u w_v du dv`. -/
theorem scat_Vw2_eq (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∫ x, V x * w x ^ 2 = (2 * π)⁻¹ ^ 6 *
      ∫ u, ∫ v, (ft V (u - v)).re * wmom V w u * wmom V w v := by
  have hVw := (scat_integrable hV hw).2.1
  have hc : Continuous fun x => V x * w x :=
    (ident_V_continuous hV).mul (ident_w_continuous hw)
  have h1 : ∫ x, V x * w x ^ 2 = ∫ x, (V x * w x) * w x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  have h2 : ∀ u, (ft (fun x => V x * w x) u).re * wmom V w u =
      (2 * π)⁻¹ ^ 3 * ∫ v, (ft V (u - v)).re * wmom V w u * wmom V w v := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [wmom]
    · have hav := scat_av hV hw u hu
      have hgp := congrArg Complex.re (scat_gp hV hw u hu)
      rw [Complex.ofReal_re] at hgp
      have hin : ∫ v, (ft V (u - v)).re * wmom V w u * wmom V w v =
          (∫ v, (ft V (u - v)).re * wmom V w v) * wmom V w u := by
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        dsimp only
        ring
      rw [ident_ft_Vw_re hV hw u, hgp, hin]
      linear_combination (wmom V w u) * hav
  rw [h1, ident_pair hc hVw hV hw]
  simp_rw [h2]
  rw [integral_const_mul]
  ring

end

end LHYUpper
