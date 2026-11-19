import LHYUpper.Model.Basic

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section

namespace LHYUpper

/-! # Maximum principle and uniqueness of the scattering solution

Proves the uniqueness of the zero-energy scattering solution of §2 for a nonnegative potential
(`scat_solution_unique`). The proof uses the nonpositivity of the Laplacian at a local maximum of a
`C²` function on `ℝ³`, the Laplacian of `‖x‖²`, and a maximum principle for `Δd = V d` on a ball and
on `ℝ³`; two solutions then satisfy `w' ≤ w`. -/

/-- At a local maximum of a one-variable function continuous at `0`, the second derivative is
nonpositive. -/
private lemma scat_deriv_deriv_nonpos_of_isLocalMax {φ : ℝ → ℝ} (hc : ContinuousAt φ 0)
    (h : IsLocalMax φ 0) : deriv (deriv φ) 0 ≤ 0 := by
  by_contra hpos
  replace hpos := not_le.mp hpos
  have hmin : IsLocalMin φ 0 :=
    isLocalMin_of_deriv_deriv_pos hpos h.deriv_eq_zero hc
  have hconst : φ =ᶠ[𝓝 0] fun _ => φ 0 := by
    filter_upwards [h, hmin] with t h1 h2
    exact le_antisymm h1 h2
  have hd : deriv φ =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    have := hconst.deriv
    simpa using this
  have : deriv (deriv φ) 0 = 0 := by
    rw [hd.deriv_eq]; simp
  linarith

/-- The second derivative of `t ↦ f (x + t • e)` at `0` is the second Fréchet derivative of `f`
at `x` in the direction `e`. -/
private lemma scat_deriv_deriv_line {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (x e : R3) :
    deriv (deriv fun t : ℝ => f (x + t • e)) 0 = iteratedFDeriv ℝ 2 f x ![e, e] := by
  set L : ℝ →L[ℝ] R3 := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) e with hL
  have hg : ContDiff ℝ 2 (fun z : R3 => f (x + z)) := hf.comp (contDiff_const.add contDiff_id)
  have h1 : (fun t : ℝ => f (x + t • e)) = (fun z : R3 => f (x + z)) ∘ L := by
    funext t; simp [hL]
  have h2 : deriv (deriv fun t : ℝ => f (x + t • e)) 0
      = iteratedFDeriv ℝ 2 (fun t : ℝ => f (x + t • e)) 0 (fun _ => 1) := by
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h1, L.iteratedFDeriv_comp_right hg 0 (le_refl 2), iteratedFDeriv_comp_add_left]
  simp only [map_zero, add_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i; fin_cases i <;> simp [hL]

/-- At a local maximum of a `C²` function on ℝ³ the Laplacian is nonpositive. -/
theorem scat_laplacian_nonpos_of_isLocalMax {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : R3}
    (h : IsLocalMax f x₀) : Laplacian.laplacian f x₀ ≤ 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [← scat_deriv_deriv_line hf x₀ _]
  have hg : Continuous fun t : ℝ => x₀ + t • (EuclideanSpace.basisFun (Fin 3) ℝ i : R3) := by
    fun_prop
  refine scat_deriv_deriv_nonpos_of_isLocalMax (hf.continuous.comp hg).continuousAt ?_
  have h0 : IsLocalMax f x₀ := h
  exact IsLocalMax.comp_continuous
    (g := fun t : ℝ => x₀ + t • (EuclideanSpace.basisFun (Fin 3) ℝ i : R3))
    (b := 0) (by simpa using h0) hg.continuousAt

/-- The second derivative at `0` of `t ↦ c + b t + t²` is `2`. -/
private lemma scat_deriv_deriv_quad (c b : ℝ) :
    deriv (deriv fun t : ℝ => c + b * t + t ^ 2) 0 = 2 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c + b * t + t ^ 2) (b + 2 * t) t := by
    intro t
    have := ((hasDerivAt_const t c).add ((hasDerivAt_id' t).const_mul b)).add
      (hasDerivAt_pow 2 t)
    exact this.congr_deriv (by simp)
  have h2 : deriv (fun t : ℝ => c + b * t + t ^ 2) = fun t => b + 2 * t :=
    funext fun t => (h1 t).deriv
  rw [h2]
  simp

/-- The Laplacian of `x ↦ ‖x‖²` on ℝ³ is the constant `6`. -/
private lemma scat_laplacian_normSq (x : R3) :
    Laplacian.laplacian (fun y : R3 => ‖y‖ ^ 2) x = 6 := by
  have hsq : ContDiff ℝ 2 (fun y : R3 => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  have key : ∀ i : Fin 3, iteratedFDeriv ℝ 2 (fun y : R3 => ‖y‖ ^ 2) x
      ![(EuclideanSpace.basisFun (Fin 3) ℝ i : R3), (EuclideanSpace.basisFun (Fin 3) ℝ i : R3)]
      = 2 := by
    intro i
    rw [← scat_deriv_deriv_line hsq x]
    have hφ : (fun t : ℝ => ‖x + t • (EuclideanSpace.basisFun (Fin 3) ℝ i : R3)‖ ^ 2)
        = fun t : ℝ => ‖x‖ ^ 2 + (2 * ⟪x, (EuclideanSpace.basisFun (Fin 3) ℝ i : R3)⟫) * t
          + t ^ 2 := by
      funext t
      rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, OrthonormalBasis.norm_eq_one]
      simp only [Real.norm_eq_abs, sq_abs]
      ring
    simp only [hφ]
    exact scat_deriv_deriv_quad _ _
  beta_reduce
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp
  norm_num

/-- The equation of a scattering solution, written for `Δw`. -/
private lemma scat_laplacian_eq {V w : R3 → ℝ} (hw : IsScatteringSolution V w) (x : R3) :
    Laplacian.laplacian w x = -(V x * (1 - w x)) := by
  have h1 := hw.eqn x
  have hsub : Laplacian.laplacian (fun y => 1 - w y) x = -Laplacian.laplacian w x := by
    have := (contDiffAt_const (c := (1 : ℝ))).laplacian_sub (hw.smooth.contDiffAt (x := x))
    have e : (fun y => 1 - w y) = (fun _ : R3 => (1 : ℝ)) - w := rfl
    rw [e, this]
    simp
  linarith

/-- The difference of two scattering solutions satisfies `Δd = V d`. -/
private lemma scat_laplacian_diff {V w w' : R3 → ℝ} (hw : IsScatteringSolution V w)
    (hw' : IsScatteringSolution V w') (x : R3) :
    Laplacian.laplacian (fun y => w' y - w y) x = V x * (w' x - w x) := by
  have := (hw'.smooth.contDiffAt (x := x)).laplacian_sub (hw.smooth.contDiffAt (x := x))
  have e : (fun y => w' y - w y) = w' - w := rfl
  rw [e, this, scat_laplacian_eq hw, scat_laplacian_eq hw']
  ring

/-- Maximum principle on a ball: if `Δd = V d` with `V ≥ 0` and `d ≤ η` on the sphere of radius
`R`, then `d ≤ η + ε R²` on the closed ball, for every `ε > 0`. -/
private lemma scat_bound_ball {V d : R3 → ℝ} (hV0 : ∀ x, 0 ≤ V x) (hd : ContDiff ℝ 2 d)
    (hΔ : ∀ x, Laplacian.laplacian d x = V x * d x) {R η ε : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (hε : 0 < ε) (hb : ∀ y : R3, ‖y‖ = R → d y ≤ η) {x : R3} (hx : ‖x‖ ≤ R) :
    d x ≤ η + ε * R ^ 2 := by
  set v : R3 → ℝ := fun y => d y + ε * ‖y‖ ^ 2 with hv
  have hvc : ContDiff ℝ 2 v := hd.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hΔv : ∀ y, Laplacian.laplacian v y = V y * d y + ε * 6 := by
    intro y
    have e : v = d + ε • (fun z : R3 => ‖z‖ ^ 2) := by
      funext z; simp [hv]
    have hsq : ContDiffAt ℝ 2 (fun z : R3 => ‖z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt
    have hsq' : ContDiffAt ℝ 2 (ε • fun z : R3 => ‖z‖ ^ 2) y := hsq.const_smul ε
    rw [e, hd.contDiffAt.laplacian_add hsq', InnerProductSpace.laplacian_smul ε hsq,
      scat_laplacian_normSq, hΔ]
    simp
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : R3) R).exists_isMaxOn
    (⟨0, by simp [hR.le]⟩ : (Metric.closedBall (0 : R3) R).Nonempty) hvc.continuous.continuousOn
  have hx₀R : ‖x₀‖ ≤ R := by simpa using hx₀
  have hv_le : v x₀ ≤ η + ε * R ^ 2 := by
    by_cases hint : ‖x₀‖ < R ∧ 0 ≤ d x₀
    · exfalso
      have hmem : x₀ ∈ Metric.ball (0 : R3) R := by simpa using hint.1
      have hloc : IsLocalMax v x₀ :=
        hmax.isLocalMax (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem)
          Metric.ball_subset_closedBall)
      have hle := scat_laplacian_nonpos_of_isLocalMax hvc hloc
      rw [hΔv] at hle
      nlinarith [mul_nonneg (hV0 x₀) hint.2]
    · have hsq : ε * ‖x₀‖ ^ 2 ≤ ε * R ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx₀R 2) hε.le
      rw [not_and_or] at hint
      rcases hint with h1 | h2
      · have h1' : ‖x₀‖ = R := le_antisymm hx₀R (not_lt.mp h1)
        have := hb x₀ h1'
        simp only [hv]
        rw [h1']
        linarith
      · have := not_le.mp h2
        simp only [hv]
        linarith
  have hxmem : x ∈ Metric.closedBall (0 : R3) R := by simpa using hx
  have hvx : v x ≤ v x₀ := isMaxOn_iff.mp hmax x hxmem
  have : d x ≤ v x := by
    simp only [hv]
    nlinarith [sq_nonneg ‖x‖]
  linarith

/-- Maximum principle on ℝ³: if `d` is `C²`, `Δd = V d` with `V ≥ 0`, and `d → 0` at infinity,
then `d ≤ 0`. -/
private lemma scat_max_principle {V d : R3 → ℝ} (hV0 : ∀ x, 0 ≤ V x) (hd : ContDiff ℝ 2 d)
    (hΔ : ∀ x, Laplacian.laplacian d x = V x * d x) (h0 : Tendsto d (cocompact R3) (𝓝 0))
    (x : R3) : d x ≤ 0 := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hev : ∀ᶠ y in cocompact R3, d y < η := h0.eventually (gt_mem_nhds hη)
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hev
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall (0 : R3)
  set R : ℝ := max (max (R₁ + 1) ‖x‖) 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR₁R : R₁ < R := lt_of_lt_of_le (lt_add_one R₁) ((le_max_left _ _).trans (le_max_left _ _))
  have hxR : ‖x‖ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hb : ∀ y : R3, ‖y‖ = R → d y ≤ η := by
    intro y hy
    have hyK : y ∉ K := fun hyK => by
      have := hR₁ hyK
      rw [mem_closedBall_zero_iff] at this
      linarith
    exact (hKsub hyK).le
  have hxle : d x ≤ η := by
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    have hR2 : 0 < R ^ 2 := by positivity
    have := scat_bound_ball hV0 hd hΔ hRpos hη.le (div_pos hε' hR2) hb hxR
    calc d x ≤ η + ε' / R ^ 2 * R ^ 2 := this
      _ = η + ε' := by field_simp
  linarith

/-- If `w` and `w'` are scattering solutions for the same nonnegative `V`, then `w' ≤ w`. -/
private lemma scat_le {V w w' : R3 → ℝ} (hV0 : ∀ x, 0 ≤ V x) (hw : IsScatteringSolution V w)
    (hw' : IsScatteringSolution V w') (x : R3) : w' x ≤ w x := by
  have h := scat_max_principle (d := fun y => w' y - w y) hV0 (hw'.smooth.sub hw.smooth)
    (scat_laplacian_diff hw hw') (by simpa using hw'.tendsto_zero.sub hw.tendsto_zero) x
  linarith

/-- Uniqueness of the zero-energy scattering solution of §2 for a nonnegative potential:
`d = w' - w` satisfies `Δd = Vd`, `d → 0`, so `d = 0` by the maximum principle. -/
theorem scat_solution_unique {V w w' : R3 → ℝ} (hV0 : ∀ x, 0 ≤ V x)
    (hw : IsScatteringSolution V w) (hw' : IsScatteringSolution V w') : w = w' := by
  funext x
  exact le_antisymm (scat_le hV0 hw' hw x) (scat_le hV0 hw hw' x)

end LHYUpper
