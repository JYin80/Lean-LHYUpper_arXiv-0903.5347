import LHYUpper.Riemann.Defs

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! # Integrals of radial functions and the shell estimate

Radial integration on `ℝ³`: `∫ f(|k|) dk = 4π ∫_0^∞ s² f(s) ds` (`integral_radial`), and the bound
for the integral of a function with singularity `|k|^{-a}` at the origin and decay `|k|^{-b}`
outside a shell (`integral_sub_setIntegral_shell`), the continuous half of the Riemann-sum lemma. -/

/-- Integrals of radial functions on ℝ³: `∫ f(|k|) dk = 4π ∫_0^∞ s² f(s) ds`. -/
theorem integral_radial (f : ℝ → ℝ) :
    ∫ k : R3, f ‖k‖ = 4 * π * ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * f s := by
  rw [integral_fun_norm_addHaar volume f, finrank_euclideanSpace_fin]
  have hv : (volume : Measure R3).real (Metric.ball 0 1) = π * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [hv]
  simp only [nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

private lemma radial_integrable {f : ℝ → ℝ}
    (hf : IntegrableOn (fun s : ℝ => s ^ 2 * f s) (Set.Ioi 0)) :
    Integrable (fun k : R3 => f ‖k‖) := by
  rw [integrable_fun_norm_addHaar volume]
  simpa [finrank_euclideanSpace_fin] using hf

/-- The radial profile `s ↦ s^{-a}` on `s ≤ r`. -/
private def inProfile (a r : ℝ) : ℝ → ℝ := (Set.Iic r).indicator (fun s : ℝ => s ^ (-a))

/-- The radial profile `s ↦ s^{-b}` on `r ≤ ofReal s`. -/
private def outProfile (b : ℝ) (r : ℝ≥0∞) : ℝ → ℝ :=
  {s : ℝ | r ≤ ENNReal.ofReal s}.indicator (fun s : ℝ => s ^ (-b))

private lemma inProfile_nonneg (a r : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ inProfile a r s := by
  unfold inProfile
  rw [Set.indicator_apply]
  split_ifs
  · positivity
  · exact le_rfl

private lemma outProfile_nonneg (b : ℝ) (r : ℝ≥0∞) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ outProfile b r s := by
  unfold outProfile
  rw [Set.indicator_apply]
  split_ifs
  · positivity
  · exact le_rfl

private lemma inProfile_spec {a : ℝ} (ha : a < 3) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun k : R3 => inProfile a r ‖k‖) ∧
      ∫ k : R3, inProfile a r ‖k‖ = 4 * π * (r ^ (3 - a) / (3 - a)) := by
  have hcongr : ∀ s ∈ Set.Ioi (0 : ℝ),
      s ^ 2 * inProfile a r s = (Set.Ioc 0 r).indicator (fun s : ℝ => s ^ (2 - a)) s := by
    intro s hs
    have hs0 : 0 < s := hs
    have h2 : s ^ 2 * s ^ (-a) = s ^ (2 - a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs0]
      norm_num
      ring_nf
    unfold inProfile
    by_cases hsr : s ≤ r
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hsr),
        Set.indicator_of_mem (show s ∈ Set.Ioc 0 r from ⟨hs0, hsr⟩), h2]
    · rw [Set.indicator_of_notMem (show s ∉ Set.Iic r from hsr),
        Set.indicator_of_notMem (show s ∉ Set.Ioc 0 r from fun h => hsr h.2), mul_zero]
  have hint : IntegrableOn (fun s : ℝ => s ^ (2 - a)) (Set.Ioc 0 r) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).1
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) (r := 2 - a) (by linarith))
    exact this
  have hI : IntegrableOn (fun s : ℝ => s ^ 2 * inProfile a r s) (Set.Ioi 0) := by
    rw [integrableOn_congr_fun hcongr measurableSet_Ioi, IntegrableOn,
      integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc]
    exact (hint.mono_set (Set.inter_subset_left)).mono_measure le_rfl
  refine ⟨radial_integrable hI, ?_⟩
  rw [integral_radial, setIntegral_congr_fun measurableSet_Ioi hcongr,
    setIntegral_indicator measurableSet_Ioc]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 r = Set.Ioc 0 r := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto
  rw [hset, ← intervalIntegral.integral_of_le hr, integral_rpow (Or.inl (by linarith))]
  have h3 : (2 - a + 1) = 3 - a := by ring
  rw [h3, Real.zero_rpow (by linarith)]
  ring


private lemma outProfile_spec {b : ℝ} (hb : 3 < b) {r : ℝ≥0∞} (hr : 0 < r) :
    Integrable (fun k : R3 => outProfile b r ‖k‖) ∧
      ∫ k : R3, outProfile b r ‖k‖ = 4 * π * ((r⁻¹).toReal ^ (b - 3) / (b - 3)) := by
  by_cases htop : r = ⊤
  · have h0 : outProfile b r = fun _ => 0 := by
      funext s
      unfold outProfile
      rw [Set.indicator_of_notMem]
      simp [htop]
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp [htop, Real.zero_rpow (show b - 3 ≠ 0 by linarith)]
  · set ρ : ℝ := r.toReal with hρ
    have hρpos : 0 < ρ := ENNReal.toReal_pos hr.ne' htop
    have hrρ : r = ENNReal.ofReal ρ := (ENNReal.ofReal_toReal htop).symm
    have hset : {s : ℝ | r ≤ ENNReal.ofReal s} = Set.Ici ρ := by
      ext s
      change r ≤ ENNReal.ofReal s ↔ ρ ≤ s
      rw [hrρ, ENNReal.ofReal_le_ofReal_iff']
      constructor
      · rintro (h | h)
        · exact h
        · linarith
      · exact Or.inl
    have hcongr : ∀ s ∈ Set.Ioi (0 : ℝ),
        s ^ 2 * outProfile b r s = (Set.Ici ρ).indicator (fun s : ℝ => s ^ (2 - b)) s := by
      intro s hs
      have hs0 : 0 < s := hs
      have h2 : s ^ 2 * s ^ (-b) = s ^ (2 - b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hs0]
        norm_num
        ring_nf
      unfold outProfile
      rw [hset]
      by_cases hsr : ρ ≤ s
      · rw [Set.indicator_of_mem (Set.mem_Ici.2 hsr),
          Set.indicator_of_mem (Set.mem_Ici.2 hsr), h2]
      · rw [Set.indicator_of_notMem (show s ∉ Set.Ici ρ from hsr),
          Set.indicator_of_notMem (show s ∉ Set.Ici ρ from hsr), mul_zero]
    have hint : IntegrableOn (fun s : ℝ => s ^ (2 - b)) (Set.Ici ρ) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_Ioi_rpow_of_lt (by linarith) hρpos
    have hI : IntegrableOn (fun s : ℝ => s ^ 2 * outProfile b r s) (Set.Ioi 0) := by
      rw [integrableOn_congr_fun hcongr measurableSet_Ioi, IntegrableOn,
        integrable_indicator_iff measurableSet_Ici, IntegrableOn,
        Measure.restrict_restrict measurableSet_Ici]
      exact hint.mono_set (Set.inter_subset_left)
    refine ⟨radial_integrable hI, ?_⟩
    rw [integral_radial, setIntegral_congr_fun measurableSet_Ioi hcongr,
      setIntegral_indicator measurableSet_Ici]
    have hset2 : Set.Ioi (0 : ℝ) ∩ Set.Ici ρ = Set.Ici ρ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith, h⟩
    rw [hset2, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hρpos]
    have h3 : (2 - b + 1) = -(b - 3) := by ring
    rw [h3, ENNReal.toReal_inv, ← hρ, Real.inv_rpow hρpos.le, ← Real.rpow_neg hρpos.le]
    rw [neg_div_neg_eq]


private lemma singDecay_continuousAt {a b C : ℝ} {F : R3 → ℝ} (hF : SingDecay a b C F) {p : R3}
    (hp : p ≠ 0) : ContinuousAt F p := by
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  refine continuousAt_of_locally_lipschitz (r := ‖p‖ / 2) (by positivity)
    (C * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b))) fun q hq => ?_
  rw [dist_eq_norm] at hq
  rw [Real.dist_eq, dist_eq_norm]
  calc |F q - F p| ≤ C * ‖q - p‖ * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b)) := hF.lip p q hp hq.le
    _ = C * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b)) * ‖q - p‖ := by ring

private lemma singDecay_aestronglyMeasurable {a b C : ℝ} {F : R3 → ℝ} (hF : SingDecay a b C F) :
    AEStronglyMeasurable F volume := by
  have hc : ContinuousOn F ({0}ᶜ : Set R3) := fun p hp =>
    (singDecay_continuousAt hF hp).continuousWithinAt
  have h := hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : R3)).compl
  rwa [restrict_compl_singleton] at h


/-- Integral outside a shell: `|∫F − ∫_A F| ≤ K C (r₁^{3−a} + r₂^{−(b−3)})`. -/
theorem integral_sub_setIntegral_shell {a b : ℝ} (ha : 0 ≤ a) (ha3 : a < 3) (hb : 3 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (F : R3 → ℝ) (r₁ : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      0 ≤ C → SingDecay a b C F → 0 ≤ r₁ → 0 < r₂ → MeasurableSet A → IsShell r₁ r₂ 0 A →
      Integrable F ∧
      |(∫ p, F p) - ∫ p in A, F p| ≤ K * C * (r₁ ^ (3 - a) + (r₂⁻¹).toReal ^ (b - 3)) := by
  have h1 : 0 < 3 - a := by linarith
  have h2 : 0 < b - 3 := by linarith
  refine ⟨4 * π * (1 / (3 - a) + 1 / (b - 3)), by positivity, ?_⟩
  intro C F r₁ r₂ A hC hF hr₁ hr₂ hA hAs
  have hpt : ∀ (s₁ : ℝ) (s₂ : ℝ≥0∞) (p : R3), p ≠ 0 → (‖p‖ ≤ s₁ ∨ s₂ ≤ ENNReal.ofReal ‖p‖) →
      ‖F p‖ ≤ C * (inProfile a s₁ ‖p‖ + outProfile b s₂ ‖p‖) := by
    intro s₁ s₂ p hp h
    have hn : 0 ≤ ‖p‖ := norm_nonneg p
    have hbd := hF.bound p hp
    rw [Real.norm_eq_abs]
    rcases h with h | h
    · have e1 : inProfile a s₁ ‖p‖ = ‖p‖ ^ (-a) := by
        unfold inProfile; rw [Set.indicator_of_mem (Set.mem_Iic.2 h)]
      have h0 := outProfile_nonneg b s₂ hn
      calc |F p| ≤ C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b)) := hbd
        _ ≤ C * ‖p‖ ^ (-a) := mul_le_mul_of_nonneg_left (min_le_left _ _) hC
        _ ≤ C * (inProfile a s₁ ‖p‖ + outProfile b s₂ ‖p‖) :=
          mul_le_mul_of_nonneg_left (by rw [e1]; linarith) hC
    · have e2 : outProfile b s₂ ‖p‖ = ‖p‖ ^ (-b) := by
        unfold outProfile
        rw [Set.indicator_of_mem (show ‖p‖ ∈ {s : ℝ | s₂ ≤ ENNReal.ofReal s} from h)]
      have h0 := inProfile_nonneg a s₁ hn
      calc |F p| ≤ C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b)) := hbd
        _ ≤ C * ‖p‖ ^ (-b) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
        _ ≤ C * (inProfile a s₁ ‖p‖ + outProfile b s₂ ‖p‖) :=
          mul_le_mul_of_nonneg_left (by rw [e2]; linarith) hC
  have hmeas := singDecay_aestronglyMeasurable hF
  have hint : Integrable F := by
    obtain ⟨hI1, -⟩ := inProfile_spec ha3 (zero_le_one : (0 : ℝ) ≤ 1)
    obtain ⟨hO1, -⟩ := outProfile_spec hb (zero_lt_one : (0 : ℝ≥0∞) < 1)
    refine Integrable.mono' ((hI1.add hO1).const_mul C) hmeas ?_
    filter_upwards [Measure.ae_ne volume (0 : R3)] with p hp
    refine hpt 1 1 p hp ?_
    rcases le_total ‖p‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (ENNReal.one_le_ofReal.2 h)
  refine ⟨hint, ?_⟩
  obtain ⟨hI, hIv⟩ := inProfile_spec ha3 hr₁
  obtain ⟨hO, hOv⟩ := outProfile_spec hb hr₂
  have hG : Integrable (fun p : R3 => C * (inProfile a r₁ ‖p‖ + outProfile b r₂ ‖p‖)) :=
    (hI.add hO).const_mul C
  have hAc : MeasurableSet Aᶜ := hA.compl
  have hdiff : (∫ p, F p) - ∫ p in A, F p = ∫ p in Aᶜ, F p := by
    rw [← integral_add_compl hA hint]; ring
  rw [hdiff]
  have hnorm : ‖∫ p in Aᶜ, F p‖ ≤
      ∫ p in Aᶜ, C * (inProfile a r₁ ‖p‖ + outProfile b r₂ ‖p‖) := by
    refine norm_integral_le_of_norm_le hG.integrableOn ?_
    rw [ae_restrict_iff' hAc]
    filter_upwards [Measure.ae_ne volume (0 : R3)] with p hp hpA
    refine hpt r₁ r₂ p hp ?_
    by_contra hcon
    push Not at hcon
    exact hpA (hAs.1 p (by linarith [hcon.1]) (by simpa using hcon.2))
  have hGv : ∫ p : R3, C * (inProfile a r₁ ‖p‖ + outProfile b r₂ ‖p‖) =
      C * (4 * π * (r₁ ^ (3 - a) / (3 - a)) +
        4 * π * ((r₂⁻¹).toReal ^ (b - 3) / (b - 3))) := by
    rw [integral_const_mul, integral_add hI hO, hIv, hOv]
  have hle : ∫ p in Aᶜ, C * (inProfile a r₁ ‖p‖ + outProfile b r₂ ‖p‖) ≤
      ∫ p, C * (inProfile a r₁ ‖p‖ + outProfile b r₂ ‖p‖) :=
    setIntegral_le_integral hG (Eventually.of_forall fun p =>
      mul_nonneg hC (add_nonneg (inProfile_nonneg a r₁ (norm_nonneg p))
        (outProfile_nonneg b r₂ (norm_nonneg p))))
  rw [hGv] at hle
  rw [Real.norm_eq_abs] at hnorm
  set X : ℝ := r₁ ^ (3 - a) with hX
  set Y : ℝ := (r₂⁻¹).toReal ^ (b - 3) with hY
  have hX0 : 0 ≤ X := Real.rpow_nonneg hr₁ _
  have hY0 : 0 ≤ Y := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have key : (1 / (3 - a) + 1 / (b - 3)) * (X + Y) =
      X / (3 - a) + Y / (b - 3) + (Y / (3 - a) + X / (b - 3)) := by ring
  have hrest : 0 ≤ Y / (3 - a) + X / (b - 3) := by positivity
  have hpi : 0 < 4 * π := by positivity
  calc |∫ p in Aᶜ, F p| ≤ C * (4 * π * (X / (3 - a)) + 4 * π * (Y / (b - 3))) :=
        hnorm.trans hle
    _ = C * (4 * π) * (X / (3 - a) + Y / (b - 3)) := by ring
    _ ≤ C * (4 * π) * ((1 / (3 - a) + 1 / (b - 3)) * (X + Y)) :=
        mul_le_mul_of_nonneg_left (by rw [key]; linarith) (by positivity)
    _ = 4 * π * (1 / (3 - a) + 1 / (b - 3)) * C * (X + Y) := by ring

end LHYUpper
