import LHYUpper.Scattering.Solution
import LHYUpper.Position.Basic

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- The periodized potential `V^P(x) = Σ_{n ∈ ℤ³} V(x + nL)` (§12). -/
def periodize (L : ℝ) (V : R3 → ℝ) (x : R3) : ℝ := ∑' n : Idx, V (x + lat L n)


/-! ### The lattice `Lℤ³` and its decay sums -/

private lemma Per_lat_apply (L : ℝ) (n : Idx) (a : Fin 3) : (lat L n) a = L * (n a : ℝ) := rfl

private lemma Per_lat_smul (c : ℝ) (n : Idx) : lat c n = c • lat 1 n := by
  ext a
  simp [Per_lat_apply]

private lemma Per_lat_add (L : ℝ) (m n : Idx) : lat L (m + n) = lat L m + lat L n := by
  ext a
  simp [Per_lat_apply, mul_add]

private lemma Per_norm_lat_mono {c L : ℝ} (hc : 0 ≤ c) (hcL : c ≤ L) (n : Idx) :
    ‖lat c n‖ ≤ ‖lat L n‖ := by
  rw [Per_lat_smul c, Per_lat_smul L, norm_smul, norm_smul, Real.norm_of_nonneg hc,
    Real.norm_of_nonneg (hc.trans hcL)]
  exact mul_le_mul_of_nonneg_right hcL (norm_nonneg _)

private lemma Per_mom_eq_lat {c : ℝ} (hc : 0 < c) (n : Idx) : mom (2 * π / c) n = lat c n := by
  ext a
  simp only [mom, Per_lat_apply]
  have : 2 * π / (2 * π / c) = c := by field_simp
  simp [this]

/-- `Σ_n (1 + |Ln|)^{-4}` converges for `L > 0`. -/
private lemma Per_summable_decay {L : ℝ} (hL : 0 < L) :
    Summable fun n : Idx => ((1 + ‖lat L n‖) ^ 4)⁻¹ := by
  obtain ⟨C, hC⟩ := scat_lattice_decay4
  set c : ℝ := min L (2 * π) with hc
  have hc0 : 0 < c := lt_min hL (by positivity)
  have hcL : c ≤ L := min_le_left _ _
  have hc2 : c ≤ 2 * π := min_le_right _ _
  have hL' : 1 ≤ 2 * π / c := by
    rw [le_div_iff₀ hc0]; linarith
  have hs := (hC (2 * π / c) hL').1
  simp_rw [Per_mom_eq_lat hc0] at hs
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have h1 : 1 + ‖lat c n‖ ≤ 1 + ‖lat L n‖ := by linarith [Per_norm_lat_mono hc0.le hcL n]
  have h2 : 0 < 1 + ‖lat c n‖ := by positivity
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le h1 4)

private lemma Per_peetre (x y : R3) : 1 + ‖y‖ ≤ (1 + ‖x + y‖) * (1 + ‖x‖) := by
  have h1 : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    calc ‖y‖ = ‖(x + y) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + y‖ + ‖x‖ := norm_sub_le _ _
  nlinarith [norm_nonneg x, norm_nonneg (x + y), mul_nonneg (norm_nonneg x) (norm_nonneg (x + y))]

private lemma Per_schwartz_decay {V : R3 → ℝ} (hV : PotentialHyp V) :
    ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ 4 * ‖V y‖ ≤ C := by
  obtain ⟨S, hS⟩ := hV.schwartz
  refine ⟨2 ^ 4 * (Finset.Iic (4, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S, fun p => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 0)) (k := 4) (n := 0)
    le_rfl le_rfl S p
  rwa [norm_iteratedFDeriv_zero, hS] at h

/-- Uniform lattice-sum bound on balls: for `‖x‖ ≤ R` the terms `V(x + Ln)` are bounded by a
summable family independent of `x`. -/
private lemma Per_bound {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) (R : ℝ) :
    ∃ u : Idx → ℝ, Summable u ∧ ∀ (n : Idx) (x : R3), ‖x‖ ≤ R → ‖V (x + lat L n)‖ ≤ u n := by
  obtain ⟨C, hC⟩ := Per_schwartz_decay hV
  refine ⟨fun n => C * (1 + R) ^ 4 * ((1 + ‖lat L n‖) ^ 4)⁻¹,
    (Per_summable_decay hL).mul_left _, fun n x hx => ?_⟩
  have h0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hy := hC (x + lat L n)
  have hp : 0 < (1 + ‖x + lat L n‖) ^ 4 := by positivity
  have hq : 0 < (1 + ‖lat L n‖) ^ 4 := by positivity
  have hP := Per_peetre x (lat L n)
  have hP4 : (1 + ‖lat L n‖) ^ 4 ≤ ((1 + ‖x + lat L n‖) * (1 + ‖x‖)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hP 4
  rw [mul_pow] at hP4
  have hR : (1 + ‖x‖) ^ 4 ≤ (1 + R) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hCn : 0 ≤ C := le_trans (by positivity) (hC 0)
  change ‖V (x + lat L n)‖ ≤ C * (1 + R) ^ 4 * ((1 + ‖lat L n‖) ^ 4)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ hq]
  calc ‖V (x + lat L n)‖ * (1 + ‖lat L n‖) ^ 4
      ≤ ‖V (x + lat L n)‖ * ((1 + ‖x + lat L n‖) ^ 4 * (1 + ‖x‖) ^ 4) :=
        mul_le_mul_of_nonneg_left hP4 (norm_nonneg _)
    _ = ((1 + ‖x + lat L n‖) ^ 4 * ‖V (x + lat L n)‖) * (1 + ‖x‖) ^ 4 := by ring
    _ ≤ C * (1 + ‖x‖) ^ 4 := mul_le_mul_of_nonneg_right hy (by positivity)
    _ ≤ C * (1 + R) ^ 4 := mul_le_mul_of_nonneg_left hR hCn

/-! ### Properties of `V^P` -/

/-- The lattice sum defining `V^P` converges. -/
theorem periodize_summable {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) (x : R3) :
    Summable fun n : Idx => V (x + lat L n) := by
  obtain ⟨u, hu, hb⟩ := Per_bound hV hL ‖x‖
  exact Summable.of_norm_bounded hu fun n => hb n x le_rfl

/-- `V^P` is continuous. -/
theorem periodize_continuous {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) :
    Continuous (periodize L V) := by
  obtain ⟨S, hS⟩ := hV.schwartz
  have hVc : Continuous V := hS ▸ S.continuous
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨u, hu, hb⟩ := Per_bound hV hL (‖x₀‖ + 1)
  have hon : ContinuousOn (fun x : R3 => ∑' n : Idx, V (x + lat L n)) (Metric.ball x₀ 1) := by
    refine continuousOn_tsum (fun n => (hVc.comp (continuous_id.add continuous_const)).continuousOn)
      hu fun n x hx => hb n x ?_
    have : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
    have h2 : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
      calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  exact hon.continuousAt (Metric.ball_mem_nhds x₀ one_pos)

/-- `V^P` is `L`-periodic. -/
theorem periodize_periodic (L : ℝ) (V : R3 → ℝ) (x : R3) (n : Idx) :
    periodize L V (x + lat L n) = periodize L V x := by
  unfold periodize
  have h : ∀ m : Idx, V (x + lat L n + lat L m) = V (x + lat L (n + m)) := fun m => by
    rw [Per_lat_add, add_assoc]
  simp_rw [h]
  exact (Equiv.addLeft n).tsum_eq (fun m => V (x + lat L m))

/-! ### Unfolding of `ℝ³` over the lattice -/

private def Per_basis {L : ℝ} (hL : 0 < L) : Module.Basis (Fin 3) ℝ R3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map (LinearEquiv.smulOfNeZero ℝ R3 L hL.ne')

private lemma Per_basis_repr {L : ℝ} (hL : 0 < L) (x : R3) (i : Fin 3) :
    (Per_basis hL).repr x i = L⁻¹ * x i := by
  simp [Per_basis, Units.smul_def]

private lemma Per_basis_apply {L : ℝ} (hL : 0 < L) (i a : Fin 3) :
    (Per_basis hL) i a = if a = i then L else 0 := by
  simp [Per_basis]

private lemma Per_mem_span {L : ℝ} (hL : 0 < L) (x : R3) :
    x ∈ Submodule.span ℤ (Set.range (Per_basis hL)) ↔ ∃ n : Idx, x = lat L n := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext a
    simp [Per_basis_apply, Per_lat_apply, Finset.sum_apply]
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    ext a
    simp [Per_basis_apply, Per_lat_apply, Finset.sum_apply]
    ring

private lemma Per_cell_eq {L : ℝ} (hL : 0 < L) : parallelepiped (Per_basis hL) = cell L := by
  rw [parallelepiped_basis_eq]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Per_basis_repr, cell]
  refine forall_congr' fun a => ?_
  rw [mul_nonneg_iff_of_pos_left (inv_pos.2 hL), inv_mul_le_iff₀ hL, mul_one]

private lemma Per_lat_injective {L : ℝ} (hL : 0 < L) : Function.Injective (lat L) := by
  intro m n h
  funext a
  have := congrArg (fun v : R3 => v a) h
  simp only [Per_lat_apply] at this
  have h2 : (m a : ℝ) = n a := mul_left_cancel₀ hL.ne' this
  exact_mod_cast h2

/-- The lattice `Lℤ³` as an additive subgroup of `ℝ³`, identified with `ℤ³`. -/
private def Per_equiv {L : ℝ} (hL : 0 < L) :
    Idx ≃ (Submodule.span ℤ (Set.range (Per_basis hL))).toAddSubgroup :=
  Equiv.ofBijective (fun n => ⟨lat L n, (Per_mem_span hL _).2 ⟨n, rfl⟩⟩)
    ⟨fun m n h => Per_lat_injective hL (congrArg Subtype.val h),
     fun g => by
       obtain ⟨n, hn⟩ := (Per_mem_span hL g.1).1 g.2
       exact ⟨n, Subtype.ext hn.symm⟩⟩

/-- Unfolding of `ℝ³` over the lattice `Lℤ³`: `∫_{ℝ³} f = Σ_n ∫_{[0,L]³} f(Ln + ·)`. -/
private lemma Per_unfold {L : ℝ} (hL : 0 < L) {f : R3 → ℂ} (hf : Integrable f) :
    ∫ y, f y = ∑' n : Idx, ∫ z in cell L, f (lat L n + z) := by
  have : Countable (Submodule.span ℤ (Set.range (Per_basis hL))).toAddSubgroup :=
    (Per_equiv hL).symm.injective.countable
  rw [(ZSpan.isAddFundamentalDomain' (Per_basis hL) volume).integral_eq_tsum'' f hf,
    ← (Per_equiv hL).tsum_eq]
  refine tsum_congr fun n => ?_
  have hae : ZSpan.fundamentalDomain (Per_basis hL) =ᵐ[volume] cell L := by
    rw [← Per_cell_eq hL]
    exact ZSpan.fundamentalDomain_ae_parallelepiped _ _
  rw [setIntegral_congr_set hae]
  rfl

/-! ### Fourier coefficients -/

private lemma Per_mom_apply (L : ℝ) (n : Idx) (a : Fin 3) :
    (mom L n) a = 2 * π / L * (n a : ℝ) := rfl

/-- Pairing of a momentum with a lattice vector: `⟨(2π/L) m, L n⟩ = 2π m·n`. -/
private lemma Per_inner_mom_lat {L : ℝ} (hL : L ≠ 0) (m n : Idx) :
    inner ℝ (mom L m) (lat L n) = 2 * π * ((∑ a, m a * n a : ℤ) : ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Per_mom_apply, Per_lat_apply,
    Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

/-- The phase `e^{-i⟨k_u, ·⟩}` is invariant under translation by `Ln`. -/
private lemma Per_phase_add_lat {L : ℝ} (hL : 0 < L) (u n : Idx) (z : R3) :
    Complex.exp (-(Complex.I * ((inner ℝ (mom L u) (lat L n + z) : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) := by
  rw [inner_add_right, Per_inner_mom_lat hL.ne']
  have h2 : -(Complex.I * ((2 * π * ((∑ a, u a * n a : ℤ) : ℝ) + inner ℝ (mom L u) z : ℝ) : ℂ)) =
      ((-(∑ a, u a * n a : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) +
        -(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ)) := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private lemma Per_cell_eq_image (L : ℝ) :
    cell L = (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) ''
      Set.pi Set.univ (fun _ : Fin 3 => Set.Icc 0 L) := by
  ext y
  constructor
  · intro hy
    exact ⟨WithLp.ofLp y, fun a _ => hy a, rfl⟩
  · rintro ⟨z, hz, rfl⟩ a
    exact hz a (Set.mem_univ a)

private lemma Per_cell_compact (L : ℝ) : IsCompact (cell L) := by
  rw [Per_cell_eq_image]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

/-- The Fourier coefficients of `V^P` on `[0, L]³` are `V_u`, `u ∈ Λ*`. -/
theorem periodize_fourier {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) (u : Idx) :
    ∫ z in cell L, Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) *
      (periodize L V z : ℂ) = ft V (mom L u) := by
  set ph : R3 → ℂ := fun z => Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ)))
    with hph
  have hphc : Continuous ph := by
    rw [hph]; fun_prop
  have hphn : ∀ z, ‖ph z‖ = 1 := fun z => by
    rw [hph]; simp only [Complex.norm_exp]; simp
  obtain ⟨S, hS⟩ := hV.schwartz
  have hVc : Continuous V := hS ▸ S.continuous
  have hVi : Integrable V := hS ▸ S.integrable
  have hcomp := Per_cell_compact L
  obtain ⟨R, hR⟩ := hcomp.isBounded.exists_norm_le
  obtain ⟨w, hw, hb⟩ := Per_bound hV hL R
  set F : Idx → R3 → ℂ := fun n z => ph z * (V (z + lat L n) : ℂ) with hF
  have hFcont : ∀ n, Continuous (F n) := fun n => by
    rw [hF]
    exact hphc.mul (Complex.continuous_ofReal.comp (hVc.comp (continuous_id.add continuous_const)))
  have hFint : ∀ n, Integrable (F n) (volume.restrict (cell L)) := fun n =>
    (hFcont n).continuousOn.integrableOn_compact hcomp
  have hFnorm : ∀ n z, ‖F n z‖ = ‖V (z + lat L n)‖ := fun n z => by
    rw [hF]; simp only [norm_mul, hphn, one_mul, Complex.norm_real]
  have hFsum : Summable fun n => ∫ z in cell L, ‖F n z‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun z => norm_nonneg _)
      (fun n => ?_) (hw.mul_right (volume.real (cell L)))
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell L)
      (f := fun z => ‖F n z‖) (C := w n) hcomp.measure_lt_top
      (fun z hz => by rw [norm_norm, hFnorm]; exact hb n z (hR z hz))
    exact (le_abs_self _).trans this
  have h1 : ∀ z, ph z * (periodize L V z : ℂ) = ∑' n, F n z := fun z => by
    rw [periodize, Complex.ofReal_tsum, ← tsum_mul_left]
  have hf : Integrable (fun y => ph y * (V y : ℂ)) := by
    refine Integrable.mono' (g := fun y => ‖V y‖) hVi.norm
      (hphc.mul (Complex.continuous_ofReal.comp hVc)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [norm_mul, hphn, one_mul, Complex.norm_real]
    exact le_rfl
  calc ∫ z in cell L, ph z * (periodize L V z : ℂ) = ∫ z in cell L, ∑' n, F n z := by
        simp_rw [h1]
    _ = ∑' n, ∫ z in cell L, F n z :=
        (integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = ∑' n : Idx, ∫ z in cell L, (fun y => ph y * (V y : ℂ)) (lat L n + z) := by
        refine tsum_congr fun n => integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hF, hph]
        rw [Per_phase_add_lat hL, add_comm (lat L n) z]
    _ = ∫ y, ph y * (V y : ℂ) := (Per_unfold hL hf).symm
    _ = ft V (mom L u) := rfl

end LHYUpper
