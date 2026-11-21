module

public import LHYUpper.TrialState.Defs

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # The momentum regions `P_L`, `P_I`, `P_H`

Elementary facts on the regions of Definition 3.1 [def1]: `P_{H,c}` of (8.1) [defPHc] as `inPHc`;
the regions `P_L`, `P_I`, `P_H` exclude the origin, are pairwise disjoint and are invariant under `n
↦ -n`; `p + p ∉ P_L` for `p ∈ P_H`; the two momenta of a soft pair creation (Definition 3.3, item 2)
are distinct and nonzero; `λ_{-k} = λ_k` for (3.15) [lambda]; and the identities `csqrt x * csqrt x
= x` and `csqrt (c x) = √c csqrt x` for the square-root convention of Definition 3.6. -/

/-- `P_{H,c}` of (8.1) [defPHc]. -/
def inPHc (ρ L kc : ℝ) (n : Idx) : Prop := inPH ρ L n ∧ ‖mom L n‖ ≤ kc

private lemma Regions_mom_neg (L : ℝ) (n : Idx) : mom L (-n) = -mom L n := by
  ext i
  simp [mom]

private lemma Regions_norm_mom_neg (L : ℝ) (n : Idx) : ‖mom L (-n)‖ = ‖mom L n‖ := by
  rw [Regions_mom_neg, norm_neg]

private lemma Regions_norm_mom_add_self (L : ℝ) (p : Idx) :
    ‖mom L (p + p)‖ = 2 * ‖mom L p‖ := by
  have : mom L (p + p) = (2 : ℝ) • mom L p := by
    ext i
    simp [mom]
    ring
  rw [this, norm_smul]
  simp

private lemma Regions_mom_zero (L : ℝ) : mom L 0 = 0 := by
  ext i
  simp [mom]

private lemma Regions_eps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < epsP ρ := by
  unfold epsP
  positivity

private lemma Regions_sqrt_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < ρ ^ (1/2 : ℝ) := by
  positivity

private lemma Regions_PL_le_one {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPL ρ L n) : ρ ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  have he : 1 < epsP ρ := Real.one_lt_rpow hlt (by norm_num)
  have hs := Regions_sqrt_pos hρ
  have h1 := h.1.trans h.2
  have h2 : epsP ρ * ρ ^ (1/2 : ℝ) ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := h1
  have h3 : epsP ρ ≤ (epsP ρ)⁻¹ := le_of_mul_le_mul_right h2 hs
  have h4 : epsP ρ * epsP ρ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h3 (Regions_eps_pos hρ).le
    rwa [mul_inv_cancel₀ (Regions_eps_pos hρ).ne'] at this
  nlinarith

private lemma Regions_sqrt_le_eps_sq {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) :
    ρ ^ (1/2 : ℝ) ≤ epsP ρ * epsP ρ := by
  have : epsP ρ * epsP ρ = ρ ^ (1/100 : ℝ) := by
    unfold epsP
    rw [← Real.rpow_add hρ]
    norm_num
  rw [this]
  exact Real.rpow_le_rpow_of_exponent_ge hρ h1 (by norm_num)

theorem Regions_PL_ne_zero {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPL ρ L n) : n ≠ 0 := by
  rintro rfl
  have h1 := h.1
  rw [Regions_mom_zero, norm_zero] at h1
  have := mul_pos (Regions_eps_pos hρ) (Regions_sqrt_pos hρ)
  linarith

theorem Regions_PI_ne_zero {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPI ρ L n) : n ≠ 0 := by
  rintro rfl
  have h1 := h.1
  rw [Regions_mom_zero, norm_zero] at h1
  have := mul_pos (inv_pos.2 (Regions_eps_pos hρ)) (Regions_sqrt_pos hρ)
  linarith

theorem Regions_PH_ne_zero {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPH ρ L n) : n ≠ 0 := by
  rintro rfl
  have h1 : epsP ρ < ‖mom L 0‖ := h
  rw [Regions_mom_zero, norm_zero] at h1
  have := Regions_eps_pos hρ
  linarith

theorem Regions_PL_PI {ρ L : ℝ} {n : Idx} (h : inPL ρ L n) : ¬ inPI ρ L n := by
  intro h'
  exact absurd h.2 (not_le.2 h'.1)

theorem Regions_PL_PH {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPL ρ L n) : ¬ inPH ρ L n := by
  intro h'
  have h1 := Regions_PL_le_one hρ h
  have h2 := Regions_sqrt_le_eps_sq hρ h1
  have he := Regions_eps_pos hρ
  have h3 : (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) ≤ epsP ρ := by
    calc (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) ≤ (epsP ρ)⁻¹ * (epsP ρ * epsP ρ) :=
          mul_le_mul_of_nonneg_left h2 (inv_pos.2 he).le
      _ = epsP ρ := by field_simp
  have h4 : epsP ρ < ‖mom L n‖ := h'
  linarith [h.2]

theorem Regions_PI_PH {ρ L : ℝ} {n : Idx} (h : inPI ρ L n) : ¬ inPH ρ L n := by
  intro h'
  have h4 : epsP ρ < ‖mom L n‖ := h'
  linarith [h.2]

theorem Regions_PL_neg {ρ L : ℝ} {n : Idx} : inPL ρ L (-n) ↔ inPL ρ L n := by
  unfold inPL
  rw [Regions_norm_mom_neg]

theorem Regions_PI_neg {ρ L : ℝ} {n : Idx} : inPI ρ L (-n) ↔ inPI ρ L n := by
  unfold inPI
  rw [Regions_norm_mom_neg]

theorem Regions_PH_neg {ρ L : ℝ} {n : Idx} : inPH ρ L (-n) ↔ inPH ρ L n := by
  unfold inPH
  rw [Regions_norm_mom_neg]

theorem Regions_PH_two {ρ L : ℝ} (hρ : 0 < ρ) {p : Idx} (h : inPH ρ L p) : ¬ inPL ρ L (p + p) := by
  intro h'
  have h1 := Regions_PL_le_one hρ h'
  have h2 := Regions_sqrt_le_eps_sq hρ h1
  have he := Regions_eps_pos hρ
  have h3 : ‖mom L (p + p)‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := h'.2
  rw [Regions_norm_mom_add_self] at h3
  have h4 : (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) ≤ epsP ρ := by
    calc (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) ≤ (epsP ρ)⁻¹ * (epsP ρ * epsP ρ) :=
          mul_le_mul_of_nonneg_left h2 (inv_pos.2 he).le
      _ = epsP ρ := by field_simp
  have h5 : epsP ρ < ‖mom L p‖ := h
  linarith

/-- The two momenta of a soft pair creation (Definition 3.3, item 2) are distinct, nonzero, and
different from `±u`. -/
theorem Regions_soft_distinct {ρ L : ℝ} (hρ : 0 < ρ) {u p₁ p₂ : Idx} (hu : inPL ρ L u)
    (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂) (hs : p₁ + p₂ = u) :
    p₁ ≠ p₂ ∧ p₁ ≠ -p₂ ∧ p₁ ≠ 0 ∧ p₂ ≠ 0 ∧ p₁ ≠ u ∧ p₁ ≠ -u ∧ p₂ ≠ u ∧ p₂ ≠ -u := by
  have hn := Regions_PL_PH hρ hu
  refine ⟨?_, ?_, Regions_PH_ne_zero hρ h₁, Regions_PH_ne_zero hρ h₂, ?_, ?_, ?_, ?_⟩
  · intro h
    apply Regions_PH_two hρ h₁
    rw [h] at hs ⊢
    rw [hs]
    exact hu
  · intro h
    have : u = 0 := by rw [← hs, h]; simp
    exact Regions_PL_ne_zero hρ hu this
  · intro h
    exact hn (h ▸ h₁)
  · intro h
    apply hn
    rw [← Regions_PH_neg, ← h]
    exact h₁
  · intro h
    exact hn (h ▸ h₂)
  · intro h
    apply hn
    rw [← Regions_PH_neg, ← h]
    exact h₂

/-- `λ_{-k} = λ_k` for (3.15) [lambda]. -/
theorem Regions_lam_neg (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) :
    lam V w ρ L (-n) = lam V w ρ L n := by
  have hft : ∀ p : R3, (ft (gfun V w) (-p)).re = (ft (gfun V w) p).re := by
    intro p
    have : ft (gfun V w) (-p) = conj (ft (gfun V w) p) := by
      unfold ft
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [inner_neg_left, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp [Complex.conj_ofReal]
    rw [this, Complex.conj_re]
  unfold lam
  by_cases h : inPL ρ L n
  · simp only [Regions_PL_neg.2 h, h, ↓reduceIte, Regions_norm_mom_neg]
  · have h' : ¬ inPL ρ L (-n) := fun h' => h (Regions_PL_neg.1 h')
    simp only [h', h, ↓reduceIte, Regions_mom_neg, norm_neg, hft]

theorem Regions_csqrt_mul_self (x : ℝ) : csqrt x * csqrt x = x := by
  unfold csqrt
  split_ifs with h
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    have : ((Real.sqrt (-x) : ℝ) : ℂ) * ((Real.sqrt (-x) : ℝ) : ℂ) = ((-x : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h']
    calc (↑(Real.sqrt (-x)) * Complex.I) * (↑(Real.sqrt (-x)) * Complex.I)
        = (↑(Real.sqrt (-x)) * ↑(Real.sqrt (-x))) * (Complex.I * Complex.I) := by ring
      _ = x := by rw [this, Complex.I_mul_I]; push_cast; ring

theorem Regions_csqrt_mul {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    csqrt (c * x) = (Real.sqrt c : ℂ) * csqrt x := by
  unfold csqrt
  by_cases hx : 0 ≤ x
  · have : 0 ≤ c * x := mul_nonneg hc hx
    simp only [this, hx, ↓reduceIte, Real.sqrt_mul hc, Complex.ofReal_mul]
  · rcases hc.eq_or_lt with rfl | hc'
    · simp
    · have hx' : c * x < 0 := mul_neg_of_pos_of_neg hc' (not_le.1 hx)
      simp only [not_le.2 hx', hx, ↓reduceIte, neg_mul_eq_mul_neg, Real.sqrt_mul hc,
        Complex.ofReal_mul]
      ring

end LHYUpper
