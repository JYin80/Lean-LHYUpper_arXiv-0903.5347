module

public import LHYUpper.Model.Basic
public import LHYUpper.Scattering.Gaussian

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section

namespace LHYUpper

/-! # Fourier transform facts for the potential and lattice sums

Basic facts on the Fourier transform of §2, `W_p = ∫ e^{-ipx} W(x) dx`: its relation to Mathlib's
`𝓕`, `W_0 = ∫ W`, conjugation and parity, the bound `‖W_p‖ ≤ ∫ W` for `W ≥ 0`, and the
Lipschitz-type bound. For a potential satisfying `PotentialHyp` it shows that `V_p` is real, even,
bounded by `V_0`, Lipschitz, Schwartz and rapidly decaying, and that the lattice sums `|Λ|⁻¹ Σ_{p ∈
Λ*} (1 + |p|)^{-4}` and `|Λ|⁻¹ Σ_{u ∈ Λ*} |V_u|` are bounded uniformly in `L ≥ 1`. -/

section
variable {V : R3 → ℝ}

/-- The Fourier transform of §2, `W_p = ∫ e^{-ipx} W(x) dx`, in terms of Mathlib's `𝓕`. -/
theorem scat_ft_eq_fourier (W : R3 → ℝ) (p : R3) :
    ft W p = 𝓕 (fun x => (W x : ℂ)) ((2 * π)⁻¹ • p) := by
  rw [Real.fourier_eq]
  unfold ft
  congr 1
  ext x
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 1
  rw [inner_smul_right, real_inner_comm]
  push_cast
  field_simp

/-- `W_0 = ∫ W`. -/
theorem scat_ft_zero (W : R3 → ℝ) : ft W 0 = ((∫ x, W x : ℝ) : ℂ) := by
  unfold ft
  simp [integral_complex_ofReal]

/-- Phase factor `e^{-i⟨p,x⟩}`. -/
private def ph (p x : R3) : ℂ := Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ)))

private lemma ph_norm (p x : R3) : ‖ph p x‖ = 1 := by
  unfold ph
  rw [Complex.norm_exp]
  simp

private lemma ph_continuous (p : R3) : Continuous (fun x => ph p x) := by
  unfold ph
  fun_prop

private lemma ft_eq_ph (W : R3 → ℝ) (p : R3) : ft W p = ∫ x, ph p x * (W x : ℂ) := rfl

/-- `\overline{W_p} = W_{-p}`. -/
private lemma ft_conj (W : R3 → ℝ) (p : R3) : (starRingEnd ℂ) (ft W p) = ft W (-p) := by
  rw [ft_eq_ph, ft_eq_ph, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  unfold ph
  rw [map_mul, ← Complex.exp_conj]
  simp [inner_neg_left]

/-- `W_{-p} = W_p` for even `W`. -/
private lemma ft_neg_of_even (W : R3 → ℝ) (hW : ∀ x, W (-x) = W x) (p : R3) :
    ft W (-p) = ft W p := by
  have h := integral_neg_eq_self (fun x : R3 => ph p x * (W x : ℂ)) volume
  rw [ft_eq_ph, ft_eq_ph, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hW x]
  unfold ph
  simp [inner_neg_left, inner_neg_right]

/-- `W_p` is real for even `W`. -/
private lemma ft_real_of_even (W : R3 → ℝ) (hW : ∀ x, W (-x) = W x) (p : R3) :
    ft W p = (((ft W p).re : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (ft W p) = ft W p := by rw [ft_conj, ft_neg_of_even W hW]
  exact (Complex.conj_eq_iff_re.1 h).symm

/-- `‖W_p‖ ≤ ∫ W` for `W ≥ 0`. -/
private lemma ft_norm_le (W : R3 → ℝ) (hW : ∀ x, 0 ≤ W x) (p : R3) :
    ‖ft W p‖ ≤ ∫ x, W x := by
  unfold ft
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul]
  have h := ph_norm p x
  unfold ph at h
  rw [h, one_mul, Complex.norm_real, Real.norm_of_nonneg (hW x)]

/-- `W_p - W_q` bounded by `‖p - q‖ ∫ ‖x‖ W` for integrable `W` with `‖x‖ W` integrable. -/
private lemma ft_sub_le (W : R3 → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hW : Integrable W)
    (hW1 : Integrable (fun x => ‖x‖ * W x)) (p q : R3) :
    ‖ft W p - ft W q‖ ≤ (∫ x, ‖x‖ * W x) * ‖p - q‖ := by
  have hint : ∀ r : R3, Integrable (fun x => Complex.exp (-(Complex.I * ((inner ℝ r x : ℝ) : ℂ))) *
      (W x : ℂ)) := by
    intro r
    refine Integrable.bdd_mul (c := 1) hW.ofReal ?_ ?_
    · exact (ph_continuous r).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => (ph_norm r x).le)
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
      have h3 : ‖Complex.exp (-(Complex.I * ((inner ℝ q x : ℝ) : ℂ)))‖ = 1 := ph_norm q x
      rw [h3, one_mul]
      refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_sub_rev]
    calc _ ≤ (‖p - q‖ * ‖x‖) * W x := by gcongr; exact hW0 x
      _ = _ := by ring
  · rw [integral_const_mul, mul_comm]

/-- A Schwartz function `S : 𝓢(R3, ℝ)` with `⇑S = V` has integrable `V` and `‖x‖ V`. -/
private lemma integrable_of_schwartz {V : R3 → ℝ} (hV : ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = V)
    (hV0 : ∀ x, 0 ≤ V x) : Integrable V ∧ Integrable (fun x => ‖x‖ * V x) := by
  obtain ⟨S, rfl⟩ := hV
  refine ⟨S.integrable, ?_⟩
  have h := S.integrable_pow_mul (volume : Measure R3) 1
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [pow_one, Real.norm_of_nonneg (hV0 x)]

/-- `V_p` is real (§2: `V_u = V̄_u`). -/
theorem scat_ft_V_real (hV : PotentialHyp V) : ∀ p, ft V p = (((ft V p).re : ℝ) : ℂ) :=
  fun p => ft_real_of_even V hV.even p

/-- `V_{-p} = V_p` (§2). -/
theorem scat_ft_V_neg (hV : PotentialHyp V) : ∀ p, ft V (-p) = ft V p :=
  fun p => ft_neg_of_even V hV.even p

/-- `|V_p| ≤ V_0 = ∫ V`. -/
theorem scat_ft_V_norm_le (hV : PotentialHyp V) : ∀ p, ‖ft V p‖ ≤ ∫ x, V x :=
  fun p => ft_norm_le V hV.nonneg p

/-- `p ↦ V_p` is Lipschitz. -/
theorem scat_ft_V_lipschitz (hV : PotentialHyp V) :
    ∃ C, ∀ p q, ‖ft V p - ft V q‖ ≤ C * ‖p - q‖ := by
  obtain ⟨h0, h1⟩ := integrable_of_schwartz hV.schwartz hV.nonneg
  exact ⟨∫ x, ‖x‖ * V x, fun p q => ft_sub_le V hV.nonneg h0 h1 p q⟩

/-- `p ↦ V_p` is a Schwartz function. -/
theorem scat_ft_V_schwartz (hV : PotentialHyp V) :
    ∃ S : SchwartzMap R3 ℂ, (S : R3 → ℂ) = ft V := by
  obtain ⟨S, rfl⟩ := hV.schwartz
  let Sc : SchwartzMap R3 ℂ := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM S
  let F : SchwartzMap R3 ℂ := SchwartzMap.fourierTransformCLM ℂ Sc
  let g : R3 ≃L[ℝ] R3 :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * π)⁻¹ : ℝ) (by positivity))
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ g F, ?_⟩
  funext p
  change 𝓕 (fun x => (S x : ℂ)) (g p) = ft S p
  rw [scat_ft_eq_fourier]
  rfl

/-- `V_p` decays faster than any power of `|p|`. -/
theorem scat_ft_V_decay (hV : PotentialHyp V) (k : ℕ) :
    ∃ C, ∀ p, (1 + ‖p‖) ^ k * ‖ft V p‖ ≤ C := by
  obtain ⟨S, hS⟩ := scat_ft_V_schwartz hV
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S, fun p => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl S p
  rwa [norm_iteratedFDeriv_zero, hS] at h

/-- The lattice index `n ∈ ℤ³` as a point of `R3`, so that `mom L n = (2π/L) • eR n`. -/
private def eR (n : Idx) : R3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => (n i : ℝ))

private lemma mom_eq (L : ℝ) (n : Idx) : mom L n = (2 * π / L) • eR n := by
  ext i
  simp [mom, eR]

/-- The unit cube `∏ [n_i - 1/2, n_i + 1/2)` centred at `eR n`. -/
private def cell (n : Idx) : Set R3 :=
  (WithLp.ofLp : R3 → (Fin 3 → ℝ)) ⁻¹'
    Set.pi Set.univ (fun i => Set.Ico ((n i : ℝ) - 1 / 2) ((n i : ℝ) + 1 / 2))

private lemma cell_measurable (n : Idx) : MeasurableSet (cell n) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).preimage
    (PiLp.volume_preserving_ofLp (Fin 3)).measurable

private lemma cell_volume (n : Idx) : volume (cell n) = 1 := by
  unfold cell
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet, Real.volume_pi_Ico]
  simp
  norm_num

private lemma cell_disjoint {n m : Idx} (h : n ≠ m) : Disjoint (cell n) (cell m) := by
  rw [Set.disjoint_left]
  intro z hn hm
  apply h
  funext i
  have h1 := hn i (Set.mem_univ i)
  have h2 := hm i (Set.mem_univ i)
  simp only [Set.mem_Ico] at h1 h2
  have h3 : n i - m i < 1 := by
    have : ((n i : ℝ) - m i) < 1 := by linarith [h1.1, h1.2, h2.1, h2.2]
    exact_mod_cast this
  have h4 : m i - n i < 1 := by
    have : ((m i : ℝ) - n i) < 1 := by linarith [h1.1, h1.2, h2.1, h2.2]
    exact_mod_cast this
  omega

private lemma norm_sub_eR_le {n : Idx} {z : R3} (hz : z ∈ cell n) : ‖z - eR n‖ ≤ 1 := by
  have h2 : ‖z - eR n‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(z - eR n).ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 / 4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hz i (Set.mem_univ i)
          simp only [Set.mem_Ico] at h1
          have e : (z - eR n).ofLp i = z.ofLp i - (n i : ℝ) := by simp [eR]
          rw [e, Real.norm_eq_abs, sq_abs]
          nlinarith [h1.1, h1.2]
      _ ≤ 1 := by simp; norm_num
  nlinarith [norm_nonneg (z - eR n)]

/-- The reference integrand `z ↦ (1 + |z|)^{-4}`. -/
private def kerr (z : R3) : ℝ := ((1 + ‖z‖) ^ 4)⁻¹

private lemma kerr_integrable : Integrable kerr := by
  have h : Integrable (fun z : R3 => (1 + ‖z‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only [kerr]
  rw [Real.rpow_neg (by positivity)]
  norm_cast

private lemma kerr_scaled_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : R3 => kerr (a • z)) :=
  kerr_integrable.comp_smul ha.ne'

private lemma kerr_scaled_integral {a : ℝ} (ha : 0 < a) :
    ∫ z : R3, kerr (a • z) = (a ^ 3)⁻¹ * ∫ z : R3, kerr z := by
  rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin, abs_of_pos (by positivity),
    smul_eq_mul]

private lemma kerr_scaled (a : ℝ) (ha : 0 < a) (z : R3) :
    kerr (a • z) = ((1 + a * ‖z‖) ^ 4)⁻¹ := by
  simp [kerr, norm_smul, abs_of_pos ha]

/-- Comparison of a lattice value with the values on its cell. -/
private lemma kerr_cell_le {a : ℝ} (ha : 0 < a) (ha' : a ≤ 2 * π) {n : Idx} {z : R3}
    (hz : z ∈ cell n) :
    ((1 + a * ‖eR n‖) ^ 4)⁻¹ ≤ (1 + 2 * π) ^ 4 * kerr (a • z) := by
  rw [kerr_scaled a ha]
  have h1 : ‖z‖ ≤ ‖eR n‖ + 1 := by
    calc ‖z‖ = ‖(z - eR n) + eR n‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - eR n‖ + ‖eR n‖ := norm_add_le _ _
      _ ≤ 1 + ‖eR n‖ := by gcongr; exact norm_sub_eR_le hz
      _ = _ := by ring
  have hA : 0 < 1 + a * ‖eR n‖ := by positivity
  have hB : 0 < 1 + a * ‖z‖ := by positivity
  have h2 : 1 + a * ‖z‖ ≤ (1 + 2 * π) * (1 + a * ‖eR n‖) := by
    have : a * ‖z‖ ≤ a * ‖eR n‖ + a := by nlinarith
    have h3 : 0 ≤ a * ‖eR n‖ := by positivity
    nlinarith [Real.pi_pos]
  have h3 : (1 + a * ‖z‖) ^ 4 ≤ ((1 + 2 * π) * (1 + a * ‖eR n‖)) ^ 4 :=
    pow_le_pow_left₀ hB.le h2 4
  rw [mul_pow] at h3
  have hA4 : 0 < (1 + a * ‖eR n‖) ^ 4 := by positivity
  have hB4 : 0 < (1 + a * ‖z‖) ^ 4 := by positivity
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hA4 hB4]
  linarith

/-- Finite partial sums of the lattice sum are bounded by a multiple of `∫ kerr`. -/
private lemma partial_sum_le {a : ℝ} (ha : 0 < a) (ha' : a ≤ 2 * π) (F : Finset Idx) :
    ∑ n ∈ F, ((1 + a * ‖eR n‖) ^ 4)⁻¹ ≤ (1 + 2 * π) ^ 4 * ((a ^ 3)⁻¹ * ∫ z : R3, kerr z) := by
  set h : R3 → ℝ := fun z => kerr (a • z) with hh
  have hint : Integrable h := kerr_scaled_integrable ha
  have hnn : ∀ z, 0 ≤ h z := fun z => by simp only [hh, kerr]; positivity
  have hcell : ∀ n, ((1 + a * ‖eR n‖) ^ 4)⁻¹ ≤ (1 + 2 * π) ^ 4 * ∫ z in cell n, h z := by
    intro n
    have hvol : volume (cell n) ≠ ⊤ := by rw [cell_volume]; exact ENNReal.one_ne_top
    have key := setIntegral_mono_on (μ := volume) (s := cell n)
      (f := fun _ => ((1 + a * ‖eR n‖) ^ 4)⁻¹) (g := fun z => (1 + 2 * π) ^ 4 * h z)
      (integrableOn_const hvol) ((hint.const_mul _).integrableOn) (cell_measurable n)
      (fun z hz => kerr_cell_le ha ha' hz)
    rw [setIntegral_const, integral_const_mul] at key
    simpa [Measure.real, cell_volume] using key
  calc ∑ n ∈ F, ((1 + a * ‖eR n‖) ^ 4)⁻¹
      ≤ ∑ n ∈ F, (1 + 2 * π) ^ 4 * ∫ z in cell n, h z := Finset.sum_le_sum fun n _ => hcell n
    _ = (1 + 2 * π) ^ 4 * ∫ z in ⋃ n ∈ F, cell n, h z := by
        rw [← Finset.mul_sum, integral_biUnion_finset F (fun n _ => cell_measurable n)
          (fun n _ m _ hnm => cell_disjoint hnm) (fun n _ => hint.integrableOn)]
    _ ≤ (1 + 2 * π) ^ 4 * ∫ z, h z := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)) (by positivity)
    _ = _ := by rw [hh, kerr_scaled_integral ha]

/-- `|Λ|⁻¹ Σ_{p ∈ Λ*} (1 + |p|)^{-4}` is bounded uniformly in `L ≥ 1`. -/
theorem scat_lattice_decay4 :
    ∃ C, ∀ L, 1 ≤ L → Summable (fun n : Idx => ((1 + ‖mom L n‖) ^ 4)⁻¹) ∧
      (L ^ 3)⁻¹ * ∑' n : Idx, ((1 + ‖mom L n‖) ^ 4)⁻¹ ≤ C := by
  refine ⟨(1 + 2 * π) ^ 4 * (((2 * π) ^ 3)⁻¹ * ∫ z : R3, kerr z), fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have ha : 0 < 2 * π / L := by positivity
  have ha' : 2 * π / L ≤ 2 * π := div_le_self (by positivity) hL
  have hnorm : ∀ n, ‖mom L n‖ = (2 * π / L) * ‖eR n‖ := fun n => by
    rw [mom_eq, norm_smul, Real.norm_of_nonneg ha.le]
  simp_rw [hnorm]
  have hnn : 0 ≤ fun n : Idx => ((1 + (2 * π / L) * ‖eR n‖) ^ 4)⁻¹ := fun n => by positivity
  have hsum := summable_of_sum_le hnn (partial_sum_le ha ha')
  refine ⟨hsum, ?_⟩
  have h2 := hsum.tsum_le_of_sum_le (partial_sum_le ha ha')
  calc (L ^ 3)⁻¹ * ∑' n : Idx, ((1 + (2 * π / L) * ‖eR n‖) ^ 4)⁻¹
      ≤ (L ^ 3)⁻¹ * ((1 + 2 * π) ^ 4 * ((((2 * π / L)) ^ 3)⁻¹ * ∫ z : R3, kerr z)) := by gcongr
    _ = _ := by field_simp

/-- `|Λ|⁻¹ Σ_{u ∈ Λ*} |V_u|` is bounded uniformly in `L ≥ 1`. -/
theorem scat_lattice_V (hV : PotentialHyp V) :
    ∃ C, ∀ L, 1 ≤ L → Summable (fun n : Idx => ‖ft V (mom L n)‖) ∧
      (L ^ 3)⁻¹ * ∑' n : Idx, ‖ft V (mom L n)‖ ≤ C := by
  obtain ⟨C4, hC4⟩ := scat_ft_V_decay hV 4
  obtain ⟨C, hC⟩ := scat_lattice_decay4
  have hC4' : 0 ≤ C4 := le_trans (by positivity) (hC4 0)
  refine ⟨C4 * C, fun L hL => ?_⟩
  obtain ⟨hs, hb⟩ := hC L hL
  have hle : ∀ n : Idx, ‖ft V (mom L n)‖ ≤ C4 * ((1 + ‖mom L n‖) ^ 4)⁻¹ := fun n => by
    have h := hC4 (mom L n)
    have hp : 0 < (1 + ‖mom L n‖) ^ 4 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    linarith
  have hsum : Summable (fun n : Idx => ‖ft V (mom L n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle (hs.mul_left C4)
  refine ⟨hsum, ?_⟩
  calc (L ^ 3)⁻¹ * ∑' n : Idx, ‖ft V (mom L n)‖
      ≤ (L ^ 3)⁻¹ * ∑' n : Idx, C4 * ((1 + ‖mom L n‖) ^ 4)⁻¹ := by
        exact mul_le_mul_of_nonneg_left (hsum.tsum_le_tsum hle (hs.mul_left C4)) (by positivity)
    _ = C4 * ((L ^ 3)⁻¹ * ∑' n : Idx, ((1 + ‖mom L n‖) ^ 4)⁻¹) := by
        rw [tsum_mul_left]; ring
    _ ≤ C4 * C := by gcongr

end

end LHYUpper
