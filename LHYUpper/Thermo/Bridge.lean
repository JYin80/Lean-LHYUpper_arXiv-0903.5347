module

public import LHYUpper.Position.Periodize
public import LHYUpper.Thermo.Fourier
public import LHYUpper.Position.Energy

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! Dirichlet trial states and the periodic ground state energy, for the duplication step after
Lemma 2.1 [thm1] (§2.1): a function supported in `[0, L]^{3N}` has the same energy as a function
of `(ℝ³)^N` with the interaction `V^P` and as a torus state of (2.1) [ham]; and a Dirichlet trial
state bounds `e₀^P` from above, by the finitely supported states `Ψ_R` of its Fourier truncations
(the limit `R → ∞` of their normalized energies, in `EReal`). -/

/-! ### Compactness, continuity and scaling for the Rayleigh quotient of a coefficient state -/

private lemma Bridge_isCompact_cell (L : ℝ) : IsCompact (cell L) := by
  have h : cell L = (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin 3 => Set.Icc 0 L) := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, fun a _ => hy a, by simp⟩
    · rintro ⟨z, hz, rfl⟩ a
      exact hz a (Set.mem_univ a)
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

private lemma Bridge_isCompact_cellN (L : ℝ) (N : ℕ) : IsCompact (cellN L N) := by
  have h : cellN L N = Set.pi Set.univ fun _ : Fin N => cell L := by
    ext x
    simp [cellN]
  rw [h]
  exact isCompact_univ_pi fun _ => Bridge_isCompact_cell L

private lemma Bridge_integrable {E : Type*} [NormedAddCommGroup E] (L : ℝ) {N : ℕ}
    {f : Conf N → E} (hf : Continuous f) : Integrable f (volume.restrict (cellN L N)) :=
  hf.continuousOn.integrableOn_compact (Bridge_isCompact_cellN L N)

private lemma Bridge_stateFn_contDiff (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (stateFn L N Ψ) := by
  have h : stateFn L N Ψ = fun x => ∑ α ∈ Ψ.support, Ψ α * symWave L N α x := by
    funext x
    rfl
  rw [h]
  exact ContDiff.sum fun α _ => contDiff_const.mul (symWave_contDiff L N α)

private lemma Bridge_kinD_continuous {N : ℕ} {Φ : Conf N → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : Continuous (kinD Φ) := by
  have h := hΦ.continuous_fderiv (by simp)
  unfold kinD
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun a _ =>
    (h.clm_apply continuous_const).norm.pow 2

private lemma Bridge_pairPot_continuous {W : R3 → ℝ} (hW : Continuous W) (N : ℕ) :
    Continuous fun x : Conf N => pairPot W x := by
  unfold pairPot
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => hW.comp ((continuous_apply i).sub (continuous_apply j)))
      fun _ => continuous_const

private lemma Bridge_num_occOf {N : ℕ} (p : Fin N → Idx) : (occOf p).num = N := by
  unfold Occ.num occOf
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp [Finsupp.sum_single_index]

private lemma Bridge_coeffState_num (L : ℝ) {N : ℕ} (R : ℕ) (Φ : Conf N → ℂ) (α : Occ)
    (h : coeffState L N R Φ α ≠ 0) : α.num = N := by
  unfold coeffState at h
  rw [Finsupp.indicator_apply] at h
  by_cases hα : α ∈ occBox N R
  · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hα
    exact Bridge_num_occOf p
  · simp [hα] at h

private lemma Bridge_stateFn_smul (L : ℝ) (N : ℕ) (c : ℂ) (Ψ : Occ →₀ ℂ) :
    stateFn L N (c • Ψ) = c • stateFn L N Ψ := by
  funext x
  simp only [stateFn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine (Finset.sum_subset Finsupp.support_smul fun α _ hα => ?_).trans ?_
  · rw [Finsupp.notMem_support_iff.1 hα, zero_mul]
  · exact Finset.sum_congr rfl fun α _ => by
      rw [Finsupp.smul_apply, smul_eq_mul, mul_assoc]

private lemma Bridge_kinD_smul {N : ℕ} (c : ℂ) {Φ : Conf N → ℂ} (hΦ : Differentiable ℝ Φ)
    (x : Conf N) : kinD (c • Φ) x = ‖c‖ ^ 2 * kinD Φ x := by
  unfold kinD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : fderiv ℝ (c • Φ) x = c • fderiv ℝ Φ x := fderiv_const_smul (hΦ x) c
  rw [h]
  simp [mul_pow]

private lemma Bridge_sq_diff_le (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (1 + 1 / t) * ‖a - b‖ ^ 2 + t * ‖b‖ ^ 2 := by
  have h1 := abs_norm_sub_norm_le a b
  have h2 := norm_nonneg a
  have h3 := norm_nonneg b
  have h4 := norm_nonneg (a - b)
  rw [abs_le] at h1
  have h5 : 2 * ‖a - b‖ * ‖b‖ ≤ ‖a - b‖ ^ 2 / t + t * ‖b‖ ^ 2 := by
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    nlinarith [sq_nonneg (‖a - b‖ - t * ‖b‖)]
  have h6 : ‖a - b‖ ^ 2 / t = 1 / t * ‖a - b‖ ^ 2 := by ring
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2]

/-- Weighted `L²` convergence on the cell: if `f_R → g` in `L²([0, L]^{3N})` and `|w| ≤ M` on the
cell, then `∫ w |f_R|² → ∫ w |g|²`. -/
private lemma Bridge_tendsto_weighted {L : ℝ} {N : ℕ} {f : ℕ → Conf N → ℂ} {g : Conf N → ℂ}
    (hf : ∀ R, Continuous (f R)) (hg : Continuous g) {w : Conf N → ℝ} (hw : Continuous w)
    {M : ℝ} (hM : ∀ x ∈ cellN L N, |w x| ≤ M)
    (h : Tendsto (fun R => ∫ x in cellN L N, ‖f R x - g x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ x in cellN L N, w x * ‖f R x‖ ^ 2) atTop
      (𝓝 (∫ x in cellN L N, w x * ‖g x‖ ^ 2)) := by
  have hmeas : MeasurableSet (cellN L N) := (Bridge_isCompact_cellN L N).isClosed.measurableSet
  have hM0 : 0 ≤ M ∨ cellN L N = ∅ := by
    by_cases hne : (cellN L N).Nonempty
    · obtain ⟨x, hx⟩ := hne
      exact Or.inl ((abs_nonneg _).trans (hM x hx))
    · exact Or.inr (Set.not_nonempty_iff_eq_empty.1 hne)
  set B : ℝ := ∫ x in cellN L N, ‖g x‖ ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg fun x => by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases hM0 with hM0 | hE
  · set t : ℝ := ε / (2 * (M * B + 1)) with ht
    have hMB : 0 ≤ M * B := mul_nonneg hM0 hB0
    have ht0 : 0 < t := div_pos hε (by positivity)
    have hev : ∀ᶠ R in atTop,
        M * (1 + 1 / t) * ∫ x in cellN L N, ‖f R x - g x‖ ^ 2 < ε / 2 := by
      have h' := h.const_mul (M * (1 + 1 / t))
      rw [mul_zero] at h'
      exact h'.eventually (gt_mem_nhds (by positivity))
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hev
    refine ⟨R₀, fun R hR => ?_⟩
    rw [Real.dist_eq]
    have hI1 : Integrable (fun x => ‖f R x - g x‖ ^ 2) (volume.restrict (cellN L N)) :=
      Bridge_integrable L (((hf R).sub hg).norm.pow 2)
    have hI2 : Integrable (fun x => ‖g x‖ ^ 2) (volume.restrict (cellN L N)) :=
      Bridge_integrable L (hg.norm.pow 2)
    have hIA : Integrable (fun x => w x * ‖f R x‖ ^ 2) (volume.restrict (cellN L N)) :=
      Bridge_integrable L (hw.mul ((hf R).norm.pow 2))
    have hIB : Integrable (fun x => w x * ‖g x‖ ^ 2) (volume.restrict (cellN L N)) :=
      Bridge_integrable L (hw.mul (hg.norm.pow 2))
    have hdiff : |(∫ x in cellN L N, w x * ‖f R x‖ ^ 2) - ∫ x in cellN L N, w x * ‖g x‖ ^ 2| ≤
        M * (1 + 1 / t) * (∫ x in cellN L N, ‖f R x - g x‖ ^ 2) + M * t * B := by
      rw [← integral_sub hIA hIB, ← Real.norm_eq_abs]
      have hb : ∫ x in cellN L N, (M * (1 + 1 / t) * ‖f R x - g x‖ ^ 2 + M * t * ‖g x‖ ^ 2) =
          M * (1 + 1 / t) * (∫ x in cellN L N, ‖f R x - g x‖ ^ 2) + M * t * B := by
        rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
          integral_const_mul]
      rw [← hb]
      refine norm_integral_le_of_norm_le ((hI1.const_mul _).add (hI2.const_mul _)) ?_
      refine (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun x hx => ?_)
      have hx' := hM x hx
      have hp := Bridge_sq_diff_le (f R x) (g x) ht0
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      calc |w x| * |‖f R x‖ ^ 2 - ‖g x‖ ^ 2|
          ≤ M * ((1 + 1 / t) * ‖f R x - g x‖ ^ 2 + t * ‖g x‖ ^ 2) :=
            mul_le_mul hx' hp (abs_nonneg _) hM0
        _ = M * (1 + 1 / t) * ‖f R x - g x‖ ^ 2 + M * t * ‖g x‖ ^ 2 := by ring
    have hMt : M * t * B < ε / 2 := by
      have : M * t * B = ε / 2 * ((M * B) / (M * B + 1)) := by
        rw [ht]
        field_simp
      rw [this]
      have h1 : (M * B) / (M * B + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      nlinarith
    have := hR₀ R hR
    linarith
  · have hz : ∀ F : ℕ → Conf N → ℝ, ∀ R, ∫ x in cellN L N, F R x = 0 := by
      intro F R
      rw [hE]
      simp
    refine ⟨0, fun R _ => ?_⟩
    rw [hz (fun R x => w x * ‖f R x‖ ^ 2) R, hE]
    simpa using hε

/-- The Rayleigh quotient of a finitely supported `N`-particle state with nonzero wave function
bounds `e₀^P` from above. -/
private lemma Bridge_e0P_le_quotient {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L)
    {N : ℕ} (Ψ : Occ →₀ ℂ) (hΨ : ∀ α, Ψ α ≠ 0 → α.num = N)
    (hpos : 0 < ∫ x in cellN L N, ‖stateFn L N Ψ x‖ ^ 2) :
    e0P L V N ≤ ((((∫ x in cellN L N, kinD (stateFn L N Ψ) x) +
      (∫ x in cellN L N, pairPot (periodize L V) x * ‖stateFn L N Ψ x‖ ^ 2)) /
        (∫ x in cellN L N, ‖stateFn L N Ψ x‖ ^ 2) / N : ℝ) : EReal) := by
  set K : ℝ := ∫ x in cellN L N, kinD (stateFn L N Ψ) x with hK
  set I : ℝ := ∫ x in cellN L N, pairPot (periodize L V) x * ‖stateFn L N Ψ x‖ ^ 2 with hI
  set c : ℝ := ∫ x in cellN L N, ‖stateFn L N Ψ x‖ ^ 2 with hc
  have hΨ0 : Ψ ≠ 0 := by
    rintro rfl
    have h0 : stateFn L N (0 : Occ →₀ ℂ) = 0 := by
      funext x
      simp [stateFn]
    rw [hc, h0] at hpos
    simp at hpos
  obtain ⟨α₀, hα₀⟩ := Finsupp.ne_iff.1 hΨ0
  have hα₀' : Ψ α₀ ≠ 0 := by simpa using hα₀
  set σ : ℝ := ∑ α ∈ Ψ.support, ‖Ψ α‖ ^ 2 with hσ
  have hσpos : 0 < σ := by
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨α₀, Finsupp.mem_support_iff.2 hα₀', ?_⟩
    positivity
  set r : ℝ := (Real.sqrt σ)⁻¹ with hr
  have hr2 : r ^ 2 = σ⁻¹ := by rw [hr, inv_pow, Real.sq_sqrt hσpos.le]
  set Ψh : Occ →₀ ℂ := (r : ℂ) • Ψ with hΨh
  have hΨh_apply : ∀ α, Ψh α = (r : ℂ) * Ψ α := fun α => by simp [hΨh]
  have hnum : ∀ α, Ψh α ≠ 0 → α.num = N := fun α h =>
    hΨ α (fun h0 => h (by rw [hΨh_apply, h0, mul_zero]))
  have hN : IsNState N Ψh := by
    refine ⟨?_, hnum⟩
    have h : HasSum (fun α => ‖Ψh α‖ ^ 2) (∑ α ∈ Ψ.support, ‖Ψh α‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero
        (fun α hα => by rw [hΨh_apply, Finsupp.notMem_support_iff.1 hα]; simp)
    convert h using 1
    simp_rw [hΨh_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← Finset.mul_sum, hr2, ← hσ, inv_mul_cancel₀ hσpos.ne']
  have hΦh : stateFn L N Ψh = (r : ℂ) • stateFn L N Ψ := Bridge_stateFn_smul L N _ Ψ
  have hdiff : Differentiable ℝ (stateFn L N Ψ) :=
    (Bridge_stateFn_contDiff L N Ψ).differentiable (by simp)
  have hnorm : r ^ 2 * c = 1 := by
    have h := stateFn_norm hL Ψh hN
    simp_rw [hΦh, Pi.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] at h
    rwa [integral_const_mul] at h
  have hcσ : c = σ := by
    rw [hr2] at hnorm
    field_simp at hnorm
    exact hnorm
  have hkin : ∫ x in cellN L N, kinD (stateFn L N Ψh) x = r ^ 2 * K := by
    simp_rw [hΦh, Bridge_kinD_smul _ hdiff, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [integral_const_mul]
  have hpot : ∫ x in cellN L N, pairPot (periodize L V) x * ‖stateFn L N Ψh x‖ ^ 2 =
      r ^ 2 * I := by
    simp_rw [hΦh, Pi.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hE : HasEnergy L V Ψh (r ^ 2 * K + r ^ 2 * I) := by
    refine ⟨r ^ 2 * K, ((r ^ 2 * I : ℝ) : ℂ), ?_, ?_, by push_cast; ring⟩
    · rw [← hkin]
      exact stateFn_kin_hasSum hL Ψh hnum
    · rw [← hpot]
      exact stateFn_pot_hasSum hV hL Ψh hnum
  refine (iInf_le_of_le Ψh (iInf_le_of_le (r ^ 2 * K + r ^ 2 * I)
    (iInf_le_of_le ⟨hN, hE⟩ le_rfl))).trans_eq ?_
  congr 2
  rw [hcσ, hr2]
  ring

/-- A function supported in `[0, L]^{3N}` has the same energy on `(ℝ³)^N` with the interaction
`Σ_{i ≠ j} V^P(x_i - x_j)` as on the torus of side `L`: the energy of (2.1) [ham] in position
space. -/
theorem energyD_periodize_eq_torusEnergy (L : ℝ) (V : R3 → ℝ) {N : ℕ} {Φ : Conf N → ℂ}
    (hΦ : tsupport Φ ⊆ cellN L N) :
    energyD (periodize L V) Φ = torusEnergy L V Φ := by
  have hz : ∀ x, x ∉ cellN L N →
      kinD Φ x + pairPot (periodize L V) x * ‖Φ x‖ ^ 2 = 0 := by
    intro x hx
    have h0 : Φ =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hΦ h)
    have h1 : Φ x = 0 := h0.self_of_nhds
    have h2 : fderiv ℝ Φ x = 0 := by
      rw [h0.fderiv_eq]
      simp
    simp [kinD, h1, h2]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm

/-- Variational bound for (2.1) [ham] by a Dirichlet trial state: a Dirichlet trial state `Φ` on
`[0, L]³` gives `e₀^P ≤ ⟨Φ, (Σ_i -Δ_i + Σ_{i ≠ j} V^P(x_i - x_j)) Φ⟩ / N` on the torus of side
`L`, with the periodized potential `V^P` of §12. -/
theorem e0P_le_energyD_periodize {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L)
    {N : ℕ} {Φ : Conf N → ℂ} (hΦ : IsDirichletTrial L N Φ) :
    e0P L V N ≤ ((energyD (periodize L V) Φ / N : ℝ) : EReal) := by
  obtain ⟨hsm, -, hts, hsym, hnorm⟩ := hΦ
  have hcont : Continuous Φ := hsm.continuous
  have hbox : tsupport Φ ⊆ cellN L N := fun x hx i a =>
    ⟨(hts hx i a).1.le, (hts hx i a).2.le⟩
  have hWc : Continuous (periodize L V) := periodize_continuous hV hL
  have hpc : Continuous fun x : Conf N => pairPot (periodize L V) x :=
    Bridge_pairPot_continuous hWc N
  obtain ⟨M, hM⟩ := (Bridge_isCompact_cellN L N).exists_bound_of_continuousOn hpc.continuousOn
  have hΦRc : ∀ R : ℕ, Continuous (stateFn L N (coeffState L N R Φ)) := fun R =>
    (Bridge_stateFn_contDiff L N _).continuous
  have hD := coeffState_tendsto_norm hL hcont hsym
  have hKt := coeffState_tendsto_kin hL (hsm.of_le (by simp)) hsym hts
  have hIt := Bridge_tendsto_weighted (L := L) hΦRc hcont hpc (M := M)
    (fun x hx => by simpa using hM x hx) hD
  have hct := Bridge_tendsto_weighted (L := L) (w := fun _ => 1) hΦRc hcont continuous_const
    (M := 1) (fun x _ => by simp) hD
  have h1 : ∫ x in cellN L N, ‖Φ x‖ ^ 2 = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hnorm]
    intro x hx
    have h0 : Φ x = 0 := by
      by_contra h
      exact hx (hbox (subset_tsupport _ h))
    simp [h0]
  simp only [one_mul, h1] at hct
  have hnum : ∀ R : ℕ, ∀ α, coeffState L N R Φ α ≠ 0 → α.num = N := fun R α h =>
    Bridge_coeffState_num L R Φ α h
  have hev : ∀ᶠ R : ℕ in atTop, 0 < ∫ x in cellN L N, ‖stateFn L N (coeffState L N R Φ) x‖ ^ 2 :=
    hct.eventually (lt_mem_nhds zero_lt_one)
  set K : ℝ := ∫ x in cellN L N, kinD Φ x with hK
  set I : ℝ := ∫ x in cellN L N, pairPot (periodize L V) x * ‖Φ x‖ ^ 2 with hI
  have hlim : Tendsto (fun R : ℕ =>
      (((∫ x in cellN L N, kinD (stateFn L N (coeffState L N R Φ)) x) +
        (∫ x in cellN L N, pairPot (periodize L V) x *
          ‖stateFn L N (coeffState L N R Φ) x‖ ^ 2)) /
        (∫ x in cellN L N, ‖stateFn L N (coeffState L N R Φ) x‖ ^ 2) / N : ℝ)) atTop
      (𝓝 ((K + I) / 1 / N)) :=
    ((hKt.add hIt).div hct one_ne_zero).div_const _
  have hKI : K + I = energyD (periodize L V) Φ := by
    have hk : Integrable (fun x => kinD Φ x) (volume.restrict (cellN L N)) :=
      Bridge_integrable L (Bridge_kinD_continuous hsm)
    have hp : Integrable (fun x => pairPot (periodize L V) x * ‖Φ x‖ ^ 2)
        (volume.restrict (cellN L N)) :=
      Bridge_integrable L (hpc.mul (hcont.norm.pow 2))
    rw [energyD_periodize_eq_torusEnergy L V hbox, torusEnergy, hK, hI, integral_add hk hp]
  rw [div_one, hKI] at hlim
  refine ge_of_tendsto (EReal.tendsto_coe.2 hlim) ?_
  exact hev.mono fun R hR => Bridge_e0P_le_quotient hV hL _ (hnum R) hR

end LHYUpper
