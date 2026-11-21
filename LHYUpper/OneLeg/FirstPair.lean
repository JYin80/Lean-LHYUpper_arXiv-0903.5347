module

public import LHYUpper.Particles.UpperIH
public import LHYUpper.Particles.UpperL
public import LHYUpper.Scattering.Lambda
public import LHYUpper.TrialState.FRatio
public import LHYUpper.OneLeg.Forms

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- `|√a √b - a| ≤ |a - b|` for `a, b ≥ 0`. -/
private theorem FP_sqrt_mul_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a * Real.sqrt b - a| ≤ |a - b| := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ a = s ^ 2 := ⟨_, Real.sqrt_nonneg a, (Real.sq_sqrt ha).symm⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ b = t ^ 2 := ⟨_, Real.sqrt_nonneg b, (Real.sq_sqrt hb).symm⟩
  rw [Real.sqrt_sq hs, Real.sqrt_sq ht]
  calc |s * t - s ^ 2| = s * |t - s| := by
        rw [show s * t - s ^ 2 = s * (t - s) by ring, abs_mul, abs_of_nonneg hs]
    _ ≤ (s + t) * |t - s| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = |s ^ 2 - t ^ 2| := by
        rw [show s ^ 2 - t ^ 2 = -((s + t) * (t - s)) by ring, abs_neg, abs_mul,
          abs_of_nonneg (by linarith : 0 ≤ s + t)]

/-- `√a √b ≤ a + b` for `a, b ≥ 0`. -/
private theorem FP_sqrt_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, sq_nonneg (Real.sqrt a - Real.sqrt b),
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- `|√x √y - x| ≤ 2|x - y|` for the square root of Definition 3.6, the step from (8.24)
[temp8.103] to (8.26). -/
theorem OneLeg_csqrt_mul_sub (x y : ℝ) : ‖csqrt x * csqrt y - x‖ ≤ 2 * |x - y| := by
  unfold csqrt
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y <;> simp only [hx, hy, ↓reduceIte]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith [FP_sqrt_mul_sub hx hy, abs_nonneg (x - y)]
  · have hy' : 0 ≤ -y := by linarith
    have hs := FP_sqrt_mul_le hx hy'
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.mul_im]
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    have h0 : 0 ≤ Real.sqrt x * Real.sqrt (-y) := by positivity
    rw [show Real.sqrt x * (Real.sqrt (-y) * 0 - 0 * 1) - 0 * (Real.sqrt (-y) * 1 + 0 * 0) - x
        = -x by ring,
      show Real.sqrt x * (Real.sqrt (-y) * 1 + 0 * 0) + 0 * (Real.sqrt (-y) * 0 - 0 * 1) - 0
        = Real.sqrt x * Real.sqrt (-y) by ring, abs_neg, abs_of_nonneg hx, abs_of_nonneg h0]
    linarith
  · have hx' : 0 ≤ -x := by linarith
    have hs := FP_sqrt_mul_le hx' hy
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.mul_im]
    rw [abs_sub_comm x y, abs_of_nonneg (by linarith : 0 ≤ y - x)]
    have h0 : 0 ≤ Real.sqrt (-x) * Real.sqrt y := by positivity
    rw [show (Real.sqrt (-x) * 0 - 0 * 1) * Real.sqrt y - (Real.sqrt (-x) * 1 + 0 * 0) * 0 - x
        = -x by ring,
      show (Real.sqrt (-x) * 0 - 0 * 1) * 0 + (Real.sqrt (-x) * 1 + 0 * 0) * Real.sqrt y - 0
        = Real.sqrt (-x) * Real.sqrt y by ring, abs_of_nonneg hx', abs_of_nonneg h0]
    linarith
  · have hx' : 0 ≤ -x := by linarith
    have hy' : 0 ≤ -y := by linarith
    have e : (Real.sqrt (-x) : ℂ) * Complex.I * ((Real.sqrt (-y) : ℂ) * Complex.I) - (x : ℂ) =
        ((-(Real.sqrt (-x) * Real.sqrt (-y) - -x) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    have := FP_sqrt_mul_sub hx' hy'
    rw [show -x - -y = -(x - y) by ring, abs_neg] at this
    linarith [abs_nonneg (x - y)]

/-- (8.25): `|λ_{v₂} - λ_{v₃}| ≤ ρ^{1/3}` for `v₂, v₃ ∈ P_H` with `v₂ + v₃ ∈ P_L`. -/
theorem OneLeg_lam_sub {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ v₂ v₃ : Idx, inPH (rhoN N) (LN N) v₂ → inPH (rhoN N) (LN N) v₃ →
      inPL (rhoN N) (LN N) (v₂ + v₃) →
      |lam V w (rhoN N) (LN N) v₂ - lam V w (rhoN N) (LN N) v₃| ≤ rhoN N ^ (1/3 : ℝ) := by
  obtain ⟨C, hC⟩ := scat_lam_sub_le hV hw
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hP : ∀ {a : ℝ}, 0 < a → Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
    intro a ha
    have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.comp hT
  have hpos : ∀ᶠ N : ℕ in atTop, rhoN N ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Particles_rhoN_LN hN).2.1
  have hT' : Tendsto rhoN atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hT, hpos⟩
  have h1 : ∀ᶠ N : ℕ in atTop, 2 * rhoN N ^ (49 / 100 : ℝ) ≤ 1 := by
    have h := (hP (by norm_num : (0 : ℝ) < 49 / 100)).const_mul 2
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have h2 : ∀ᶠ N : ℕ in atTop, max C 0 * rhoN N ^ (11 / 75 : ℝ) ≤ 1 := by
    have h := (hP (by norm_num : (0 : ℝ) < 11 / 75)).const_mul (max C 0)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((eventually_ge_atTop 1).and (h1.and (h2.and (hT'.eventually hC))))
  refine ⟨N₀, fun N hN v₂ v₃ h₂ h₃ hs => ?_⟩
  obtain ⟨hN1, hq1, hq2, hlip⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N
  have he : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have e2 : epsP ρ ^ 2 = ρ ^ (1 / 100 : ℝ) := by
    rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have e4 : epsP ρ ^ 4 = ρ ^ (1 / 50 : ℝ) := by
    rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have es : ρ ^ (1 / 2 : ℝ) = ρ ^ (49 / 100 : ℝ) * ρ ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_add hρ]
    norm_num
  have es' : ρ ^ (1 / 2 : ℝ) = ρ ^ (1 / 3 : ℝ) * ρ ^ (11 / 75 : ℝ) * ρ ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have hp : ‖mom L (v₂ + v₃)‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) := hs.2
  have hsmall : (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) ≤ epsP ρ / 2 := by
    rw [inv_mul_le_iff₀ he, es]
    have h01 : 0 < ρ ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hρ _
    nlinarith [e2]
  have key := hlip L v₂ v₃ (le_of_lt h₂) (le_of_lt h₃) (hp.trans hsmall)
  have hpn : 0 ≤ ‖mom L (v₂ + v₃)‖ := norm_nonneg _
  have hC' : C / epsP ρ ^ 3 * ‖mom L (v₂ + v₃)‖ ≤
      max C 0 / epsP ρ ^ 3 * ((epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ)) := by
    have h3 : C / epsP ρ ^ 3 ≤ max C 0 / epsP ρ ^ 3 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    exact (mul_le_mul_of_nonneg_right h3 hpn).trans
      (mul_le_mul_of_nonneg_left hp (div_nonneg (le_max_right _ _) (by positivity)))
  refine key.trans (hC'.trans ?_)
  have e : max C 0 / epsP ρ ^ 3 * ((epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ)) =
      (max C 0 * ρ ^ (11 / 75 : ℝ)) * ρ ^ (1 / 3 : ℝ) := by
    rw [es']
    have h4 : epsP ρ ^ 3 * epsP ρ = ρ ^ (1 / 50 : ℝ) := by rw [← e4]; ring
    have h50 : 0 < ρ ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hρ _
    field_simp
    rw [← h4]
    ring
  rw [e]
  have h13 : 0 ≤ ρ ^ (1 / 3 : ℝ) := Real.rpow_nonneg hρ.le _
  nlinarith

/-! ### The state `β = 𝓐^{v₁, v₂, v₃} α` and the coefficient of `a†_0 a†_{v₁} a_{v₂} a_{v₃}` -/

/-- The coefficient `√((α(v₃) + 1)(α(v₂) + 1) α(v₁) α(0))` of
`⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩`. -/
private def FP_c (v₁ v₂ v₃ : Idx) (α : Occ) : ℝ :=
  Real.sqrt ((α v₃ : ℝ) + 1) * Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt (α v₁ : ℝ) *
    Real.sqrt (α 0 : ℝ)

private theorem FP_a4_core {v₁ v₂ v₃ : Idx} (h1 : v₁ ≠ 0) (h2 : v₂ ≠ 0) (h3 : v₃ ≠ 0)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) (γ : Occ) :
    softPair v₁ v₂ v₃ (γ + Finsupp.single v₁ 1 + Finsupp.single 0 1) =
        γ + Finsupp.single v₂ 1 + Finsupp.single v₃ 1 ∧
      a4 0 v₁ v₂ v₃ (γ + Finsupp.single v₂ 1 + Finsupp.single v₃ 1) =
        (FP_c v₁ v₂ v₃ (γ + Finsupp.single v₁ 1 + Finsupp.single 0 1),
          γ + Finsupp.single v₁ 1 + Finsupp.single 0 1) := by
  constructor
  · ext n
    rw [MBasic_softPair_apply]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rw [a4_of_add]
    refine Prod.ext ?_ rfl
    have e3 : (γ + Finsupp.single v₂ 1 + Finsupp.single v₃ 1 : Occ) v₃ =
        (γ + Finsupp.single v₁ 1 + Finsupp.single 0 1 : Occ) v₃ + 1 := by
      simp [h3.symm, h13, h23]
    have e2 : (γ + Finsupp.single v₂ 1 : Occ) v₂ =
        (γ + Finsupp.single v₁ 1 + Finsupp.single 0 1 : Occ) v₂ + 1 := by
      simp [h2.symm, h12]
    have e1 : (γ + Finsupp.single v₁ 1 : Occ) v₁ =
        (γ + Finsupp.single v₁ 1 + Finsupp.single 0 1 : Occ) v₁ := by
      simp [h1.symm]
    simp only [FP_c]
    rw [e3, e2, e1]
    push_cast
    ring

private theorem FP_a4_fwd {v₁ v₂ v₃ : Idx} (h1 : v₁ ≠ 0) (h2 : v₂ ≠ 0) (h3 : v₃ ≠ 0)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) (β : Occ)
    (hc : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) :
    β = softPair v₁ v₂ v₃ (a4 0 v₁ v₂ v₃ β).2 ∧ 1 ≤ (a4 0 v₁ v₂ v₃ β).2 0 ∧
      1 ≤ (a4 0 v₁ v₂ v₃ β).2 v₁ ∧ (a4 0 v₁ v₂ v₃ β).1 = FP_c v₁ v₂ v₃ (a4 0 v₁ v₂ v₃ β).2 := by
  obtain ⟨γ, rfl⟩ := a4_exists_add 0 v₁ v₂ v₃ β hc
  obtain ⟨hs, ha⟩ := FP_a4_core h1 h2 h3 h12 h13 h23 γ
  rw [ha, hs]
  refine ⟨rfl, ?_, ?_, rfl⟩ <;> simp [h1, h1.symm]

private theorem FP_a4_bwd {v₁ v₂ v₃ : Idx} (h1 : v₁ ≠ 0) (h2 : v₂ ≠ 0) (h3 : v₃ ≠ 0)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) (α : Occ) (h0 : 1 ≤ α 0)
    (h1' : 1 ≤ α v₁) :
    a4 0 v₁ v₂ v₃ (softPair v₁ v₂ v₃ α) = (FP_c v₁ v₂ v₃ α, α) := by
  have hα : α - Finsupp.single 0 1 - Finsupp.single v₁ 1 + Finsupp.single v₁ 1 +
      Finsupp.single 0 1 = α := by
    ext n
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    by_cases a : 0 = n <;> by_cases b : v₁ = n <;> subst_vars <;> simp_all
  obtain ⟨hs, ha⟩ := FP_a4_core h1 h2 h3 h12 h13 h23 (α - Finsupp.single 0 1 - Finsupp.single v₁ 1)
  rw [hα] at hs ha
  rw [hs, ha]

private theorem FP_c_pos (v₁ v₂ v₃ : Idx) {α : Occ} (h0 : 1 ≤ α 0) (h1 : 1 ≤ α v₁) :
    0 < FP_c v₁ v₂ v₃ α := by
  have a0 : (0 : ℝ) < α 0 := by exact_mod_cast h0
  have a1 : (0 : ℝ) < α v₁ := by exact_mod_cast h1
  unfold FP_c
  positivity

/-! ### The trial state on and off `M` -/

private theorem FP_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  rw [FIdentities_trialState] at h
  by_contra hm
  exact h (by simp [hm])

private theorem FP_psi {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : InM (rhoN N) (LN N) kc N α) :
    trialState V w kc N α = (CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) α := by
  rw [FIdentities_trialState]
  simp [h]

private theorem FP_norm_csqrt (x : ℝ) : ‖csqrt x‖ = Real.sqrt |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg h]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_neg (not_le.1 h)]

/-! ### One pair in case (8.2): the two kinds of terms -/

/-- In case (8.2) the four legs `0, v₁, v₂, v₁ - v₂` are pairwise distinct. -/
private theorem FP_legs {ρ L kc : ℝ} (hρ : 0 < ρ) {v₁ v₂ : Idx} (hc : OneLeg_case1 ρ L kc v₁ v₂) :
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ - v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₁ - v₂ ∧ v₂ ≠ v₁ - v₂ := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨Regions_PL_ne_zero hρ h1, Regions_PH_ne_zero hρ h2.1, Regions_PH_ne_zero hρ h3.1,
    fun e => Regions_PL_PH hρ h1 (e ▸ h2.1), fun e => Regions_PL_PH hρ h1 (e ▸ h3.1), ?_⟩
  intro e
  apply Regions_PH_two hρ h2.1
  have : v₂ + v₂ = v₁ := by
    nth_rewrite 2 [e]
    exact add_sub_cancel v₂ v₁
  rw [this]
  exact h1

/-- (5.7) [properf4] for the pair of case (8.2): for `α ∈ M_{v₁}^s`, the term of
`⟨a†_0 a†_{v₁} a_{v₂} a_{v₃}⟩_Ψ` at `β = 𝓐^{v₁, v₂, v₃} α` is
`2 csqrt(λ_{v₂}) csqrt(λ_{v₃}) |Λ|⁻¹ α(0) α(v₁) √((α(v₂) + 1)(α(v₃) + 1)) |Ψ(α)|²`, (8.19)
[temp8.96]. -/
private theorem FP_termII {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {v₁ v₂ : Idx}
    (hc : OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂) (α : Occ) (h0 : 1 ≤ α 0) (h1 : 1 ≤ α v₁)
    (hsym : α v₁ = α (-v₁)) :
    conj (trialState V w kc N α) * (FP_c v₁ v₂ (v₁ - v₂) α : ℂ) *
        trialState V w kc N (softPair v₁ v₂ (v₁ - v₂) α) =
      ((2 / LN N ^ 3 : ℝ) : ℂ) * (csqrt (lam V w (rhoN N) (LN N) v₂) *
        csqrt (lam V w (rhoN N) (LN N) (v₁ - v₂))) *
      (((α 0 : ℝ) * α v₁ * (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α (v₁ - v₂) : ℝ) + 1)) *
        ‖trialState V w kc N α‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  by_cases hΨ : trialState V w kc N α = 0
  · simp [hΨ]
  have hαM := FP_inM hΨ
  have hs : v₂ + (v₁ - v₂) = v₁ := add_sub_cancel v₂ v₁
  have hβM : InM (rhoN N) (LN N) kc N (softPair v₁ v₂ (v₁ - v₂) α) :=
    InM.soft hαM hc.1 hsym hs hc.2.1.1 hc.2.2.1 hc.2.1.2 hc.2.2.2 h0 h1
  have hf := Lemma5_1_properf4 (V := V) (w := w) hρ hL hc.1 hc.2.1.1 hc.2.2.1 hs ⟨hαM, hsym⟩ hβM
  set ψ := trialState V w kc N α with hψ
  set c2 := csqrt (lam V w (rhoN N) (LN N) v₂)
  set c3 := csqrt (lam V w (rhoN N) (LN N) (v₁ - v₂))
  set L3 := LN N ^ 3 with hL3def
  have hL3 : 0 < L3 := by positivity
  set K : ℝ := 2 * Real.sqrt ((α 0 : ℝ) / L3) * Real.sqrt ((α v₁ : ℝ) / L3) with hK
  have hΨβ : trialState V w kc N (softPair v₁ v₂ (v₁ - v₂) α) = (K : ℂ) * c2 * c3 * ψ := by
    rw [FP_psi hβM, hψ, FP_psi hαM, hf]
    ring
  have hr : FP_c v₁ v₂ (v₁ - v₂) α * K = 2 / L3 * ((α 0 : ℝ) * α v₁ *
      (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α (v₁ - v₂) : ℝ) + 1))) := by
    rw [hK, Real.sqrt_div' _ hL3.le, Real.sqrt_div' _ hL3.le]
    set x0 : ℝ := (α 0 : ℝ)
    set x1 : ℝ := (α v₁ : ℝ)
    have e0 : Real.sqrt x0 * Real.sqrt x0 = x0 := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have e1 : Real.sqrt x1 * Real.sqrt x1 = x1 := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have eL : L3⁻¹ = (Real.sqrt L3)⁻¹ * (Real.sqrt L3)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hL3.le]
    unfold FP_c
    set s2 := Real.sqrt ((α v₂ : ℝ) + 1)
    set s3 := Real.sqrt ((α (v₁ - v₂) : ℝ) + 1)
    set l := Real.sqrt L3
    linear_combination (2 * s3 * s2 * l⁻¹ * l⁻¹ * Real.sqrt x1 * Real.sqrt x1) * e0 +
      (2 * s3 * s2 * l⁻¹ * l⁻¹ * x0) * e1 - (2 * x0 * x1 * s2 * s3) * eL
  have hr' := congrArg (fun x : ℝ => (x : ℂ)) hr
  have hcm := Complex.conj_mul' ψ
  rw [hΨβ]
  push_cast at hr' ⊢
  linear_combination ((FP_c v₁ v₂ (v₁ - v₂) α : ℂ) * K * c2 * c3) * hcm +
    (c2 * c3 * (‖ψ‖ : ℂ) ^ 2) * hr'

/-- (5.8) [properf5] for the pair of case (8.2): for `α ∈ M_{v₁}^a` the term at
`β = 𝓐^{v₁, v₂, v₃} α` satisfies
`√|λ_{v₂} λ_{v₃}| |Ψ(α)| c |Ψ(β)| = 2|λ_{v₁}| α(v₁) √((α(v₂) + 1)(α(v₃) + 1)) |Ψ(β)|²`, the step
(8.17)–(8.18) [sumfbe01]. -/
private theorem FP_termI {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {v₁ v₂ : Idx}
    (hc : OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂) (α : Occ)
    (hasym : α v₁ ≠ α (-v₁)) (hαM : InM (rhoN N) (LN N) kc N α)
    (hβM : InM (rhoN N) (LN N) kc N (softPair v₁ v₂ (v₁ - v₂) α)) :
    (Real.sqrt |lam V w (rhoN N) (LN N) v₂| * Real.sqrt |lam V w (rhoN N) (LN N) (v₁ - v₂)|) *
        (‖trialState V w kc N α‖ * FP_c v₁ v₂ (v₁ - v₂) α *
          ‖trialState V w kc N (softPair v₁ v₂ (v₁ - v₂) α)‖) =
      2 * |lam V w (rhoN N) (LN N) v₁| * α v₁ *
        (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α (v₁ - v₂) : ℝ) + 1)) *
        ‖trialState V w kc N (softPair v₁ v₂ (v₁ - v₂) α)‖ ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : v₂ + (v₁ - v₂) = v₁ := add_sub_cancel v₂ v₁
  have hf := Lemma5_1_properf5_mul (V := V) (w := w) hρ hL hc.1 hc.2.1.1 hc.2.2.1 hs
    ⟨hαM, hasym⟩ hβM
  set L3 := LN N ^ 3 with hL3def
  have hL3 : 0 < L3 := by positivity
  have hΨ : ((2 * lam V w (rhoN N) (LN N) v₁ * Real.sqrt ((α v₁ : ℝ) / L3) : ℝ) : ℂ) *
        trialState V w kc N (softPair v₁ v₂ (v₁ - v₂) α) =
      ((Real.sqrt ((α 0 : ℝ) / L3) : ℝ) : ℂ) * csqrt (lam V w (rhoN N) (LN N) v₂) *
        csqrt (lam V w (rhoN N) (LN N) (v₁ - v₂)) * trialState V w kc N α := by
    rw [FP_psi hβM, FP_psi hαM]
    linear_combination (CN V w kc N : ℂ) * hf
  have hn := congrArg norm hΨ
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, FP_norm_csqrt] at hn
  rw [abs_two, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_div' _ hL3.le, Real.sqrt_div' _ hL3.le] at hn
  set A := ‖trialState V w kc N α‖
  set B := ‖trialState V w kc N (softPair v₁ v₂ (v₁ - v₂) α)‖
  set m := |lam V w (rhoN N) (LN N) v₁|
  set s := Real.sqrt |lam V w (rhoN N) (LN N) v₂| * Real.sqrt |lam V w (rhoN N) (LN N) (v₁ - v₂)|
  set a0 := Real.sqrt (α 0 : ℝ)
  set a1 := Real.sqrt (α v₁ : ℝ)
  set l := Real.sqrt L3
  have hl : 0 < l := Real.sqrt_pos.2 hL3
  have key : a0 * s * A = 2 * m * a1 * B := by
    have e : 2 * m * (a1 / l) * B = a0 / l * Real.sqrt |lam V w (rhoN N) (LN N) v₂| *
        Real.sqrt |lam V w (rhoN N) (LN N) (v₁ - v₂)| * A := hn
    field_simp at e
    linear_combination -e
  have e1 : a1 * a1 = (α v₁ : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold FP_c
  linear_combination
    (Real.sqrt ((α (v₁ - v₂) : ℝ) + 1) * Real.sqrt ((α v₂ : ℝ) + 1) * a1 * B) * key +
    (2 * m * Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α (v₁ - v₂) : ℝ) + 1) * B ^ 2) * e1

/-! ### The sum over `β` and its split by `F(α) = 0` -/

/-- The summand `conj(Ψ(α)) c Ψ(β)` of `⟨a†_0 a†_{v₁} a_{v₂} a_{v₃}⟩_Ψ`, `α = T(β)`. -/
private def FP_t (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) (β : Occ) : ℂ :=
  conj (Ψ (a4 0 v₁ v₂ v₃ β).2) * ((a4 0 v₁ v₂ v₃ β).1 : ℂ) * Ψ β

/-- The summands with `α = T(β) ∈ M_{v₁}^a`, i.e. `F(β) = 0`, (8.17). -/
private def FP_tI (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) (β : Occ) : ℂ :=
  if (a4 0 v₁ v₂ v₃ β).2 v₁ = (a4 0 v₁ v₂ v₃ β).2 (-v₁) then 0 else FP_t Ψ v₁ v₂ v₃ β

/-- `α(0) α(v₁) √((α(v₂) + 1)(α(v₃) + 1)) |Ψ(α)|²` on `M_{v₁}^s`, the summand of (8.19)
[temp8.96]. -/
private def FP_h (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) (α : Occ) : ℝ :=
  (if α v₁ = α (-v₁) then
    (α 0 : ℝ) * α v₁ * (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α v₃ : ℝ) + 1)) else 0) *
    ‖Ψ α‖ ^ 2

private theorem FP_le_num (α : Occ) (u : Idx) : α u ≤ α.num := by
  by_cases hu : u ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hu
  · rw [Finsupp.notMem_support_iff.mp hu]
    exact Nat.zero_le _

private theorem FP_occ_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) {α : Occ} (h : Ψ α ≠ 0)
    (u : Idx) : (α u : ℝ) ≤ N := by
  exact_mod_cast (FP_le_num α u).trans (hΨ.2 α h).le

private theorem FP_summ {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (f : Occ → ℝ) (B : ℝ)
    (hf : ∀ α, Ψ α ≠ 0 → |f α| ≤ B) : Summable fun α => f α * ‖Ψ α‖ ^ 2 := by
  refine Summable.of_norm_bounded (hΨ.1.summable.mul_left B) (fun α => ?_)
  by_cases h : Ψ α = 0
  · simp [h]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Ψ α‖)]
    exact mul_le_mul_of_nonneg_right (hf α h) (sq_nonneg _)

private theorem FP_sqrt_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  nlinarith [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ x), Real.one_le_sqrt.2 hx]

/-- Reindexing `β ↦ α = T(β)` of the sum over `M_{v₁}^s` (the map `T` is injective, and onto
`{α : α(0), α(v₁) ≥ 1}` by `β = 𝓐^{v₁, v₂, v₃} α`). -/
private theorem FP_reindex {v₁ v₂ v₃ : Idx} (h1 : v₁ ≠ 0) (h2 : v₂ ≠ 0) (h3 : v₃ ≠ 0)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) (Ψ : Occ → ℂ) :
    ∑' β : Occ, (if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then FP_h Ψ v₁ v₂ v₃ (a4 0 v₁ v₂ v₃ β).2 else 0) =
      ∑' α : Occ, FP_h Ψ v₁ v₂ v₃ α := by
  symm
  set g : Occ → ℝ := fun β =>
    if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then FP_h Ψ v₁ v₂ v₃ (a4 0 v₁ v₂ v₃ β).2 else 0 with hg
  have hsupp : ∀ x : Function.support g, (a4 0 v₁ v₂ v₃ x.1).1 ≠ 0 := by
    intro x hx
    apply x.2
    simp [hg, hx]
  refine tsum_eq_tsum_of_ne_zero_bij (fun x => (a4 0 v₁ v₂ v₃ x.1).2) ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (a4_injOn 0 v₁ v₂ v₃ (hsupp x) (hsupp y) hxy)
  · intro α hα
    have hα' : FP_h Ψ v₁ v₂ v₃ α ≠ 0 := hα
    have h0 : 1 ≤ α 0 := by
      by_contra h
      apply hα'
      simp [FP_h, show α 0 = 0 by omega]
    have h1' : 1 ≤ α v₁ := by
      by_contra h
      apply hα'
      simp [FP_h, show α v₁ = 0 by omega]
    have hb := FP_a4_bwd h1 h2 h3 h12 h13 h23 α h0 h1'
    refine ⟨⟨softPair v₁ v₂ v₃ α, ?_⟩, ?_⟩
    · change g _ ≠ 0
      simp only [hg, hb, ne_eq, (FP_c_pos v₁ v₂ v₃ h0 h1').ne', not_false_eq_true, ↓reduceIte]
      exact hα'
    · simp only [hb]
  · intro x
    change FP_h Ψ v₁ v₂ v₃ (a4 0 v₁ v₂ v₃ x.1).2 = g x.1
    simp only [hg, ne_eq, hsupp x, not_false_eq_true, ↓reduceIte]

/-- (8.19) [temp8.96]: `⟨a†_0 a†_{v₁} a_{v₂} a_{v₃}⟩_Ψ` is the sum over `F(β) = 0` plus
`2 csqrt(λ_{v₂}) csqrt(λ_{v₃}) |Λ|⁻¹ Σ_{α ∈ M_{v₁}^s} α(0) α(v₁) √((α(v₂) + 1)(α(v₃) + 1))
|Ψ(α)|²`. -/
private theorem FP_split {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {v₁ v₂ : Idx}
    (hc : OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂) :
    OneLeg_expA (trialState V w kc N) v₁ v₂ (v₁ - v₂) =
      (∑' β, FP_tI (trialState V w kc N) v₁ v₂ (v₁ - v₂) β) +
        ((2 / LN N ^ 3 : ℝ) : ℂ) * (csqrt (lam V w (rhoN N) (LN N) v₂) *
          csqrt (lam V w (rhoN N) (LN N) (v₁ - v₂))) *
        ((∑' α, FP_h (trialState V w kc N) v₁ v₂ (v₁ - v₂) α : ℝ) : ℂ) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := FP_legs hρ hc
  set Ψ := trialState V w kc N with hΨdef
  have hΨ : IsNState N Ψ := Normalization_isNState V w kc hN
  have hsn : Summable fun β => ‖FP_t Ψ v₁ v₂ (v₁ - v₂) β‖ :=
    Expect.id4a_summable N Ψ hΨ 0 v₁ v₂ (v₁ - v₂)
  have hsI : Summable (FP_tI Ψ v₁ v₂ (v₁ - v₂)) := by
    refine Summable.of_norm_bounded hsn (fun β => ?_)
    unfold FP_tI
    split_ifs <;> simp
  have hst : Summable (FP_t Ψ v₁ v₂ (v₁ - v₂)) := hsn.of_norm
  have hpt : ∀ β, FP_t Ψ v₁ v₂ (v₁ - v₂) β - FP_tI Ψ v₁ v₂ (v₁ - v₂) β =
      ((2 / LN N ^ 3 : ℝ) : ℂ) * (csqrt (lam V w (rhoN N) (LN N) v₂) *
        csqrt (lam V w (rhoN N) (LN N) (v₁ - v₂))) *
      ((if (a4 0 v₁ v₂ (v₁ - v₂) β).1 ≠ 0 then
        FP_h Ψ v₁ v₂ (v₁ - v₂) (a4 0 v₁ v₂ (v₁ - v₂) β).2 else 0 : ℝ) : ℂ) := by
    intro β
    unfold FP_tI
    by_cases hc0 : (a4 0 v₁ v₂ (v₁ - v₂) β).1 = 0
    · simp [FP_t, hc0]
    obtain ⟨hb, h0, h1', hcoef⟩ := FP_a4_fwd h1 h2 h3 h12 h13 h23 β hc0
    simp only [ne_eq, hc0, not_false_eq_true, ↓reduceIte]
    unfold FP_t
    rw [hcoef]
    generalize (a4 0 v₁ v₂ (v₁ - v₂) β).2 = α at hb h0 h1' ⊢
    subst hb
    by_cases hsym : α v₁ = α (-v₁)
    · rw [FP_h, ite_eq_left hsym, ite_eq_left hsym, sub_zero]
      exact FP_termII hN hc α h0 h1' hsym
    · simp [hsym, FP_h]
  have e1 : OneLeg_expA Ψ v₁ v₂ (v₁ - v₂) = ∑' β, FP_t Ψ v₁ v₂ (v₁ - v₂) β := rfl
  rw [e1, ← FP_reindex h1 h2 h3 h12 h13 h23 Ψ, Complex.ofReal_tsum, ← tsum_mul_left,
    ← tsum_congr hpt, hst.tsum_sub hsI]
  ring

/-- (8.17)–(8.18) [sumfbe01]: the terms with `F(β) = 0` add up to at most `4 C g₀ ρ³ ε⁻⁷` when
`Q_Ψ(v₂, v₃) ≤ C |λ_{v₂} λ_{v₃}| ρ⁴ ε⁻⁴`, the bound (5.42) [boundpsifixeduv]. -/
private theorem FP_partI {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {v₁ v₂ : Idx} (hc : OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂)
    {C : ℝ} (hC : 0 ≤ C)
    (h42 : Expect.Q (trialState V w kc N) [v₂, v₁ - v₂] ≤
      C * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) (v₁ - v₂)| * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4) :
    ‖∑' β, FP_tI (trialState V w kc N) v₁ v₂ (v₁ - v₂) β‖ ≤
      4 * C * g0 V w * rhoN N ^ 3 / epsP (rhoN N) ^ 7 := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := FP_legs hρ hc
  have hg := scat_g0_pos hV hw
  have hl1 := scat_lam_PL hV hw (rhoN N) hρ (LN N) v₁ hc.1
  have b2 := scat_lam_PH hV hw (rhoN N) hρ (LN N) v₂ hc.2.1.1
  have b3 := scat_lam_PH hV hw (rhoN N) hρ (LN N) (v₁ - v₂) hc.2.2.1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set Ψ := trialState V w kc N with hΨdef
  have hΨ : IsNState N Ψ := Normalization_isNState V w kc hN
  set e := epsP ρ with hedef
  have he : 0 < e := Real.rpow_pos_of_pos hρ _
  have he1 : e ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hmc : mc ρ = e⁻¹ := by rw [mc, hedef, epsP, Real.rpow_neg hρ.le]
  set l₂ := lam V w ρ L v₂
  set l₃ := lam V w ρ L (v₁ - v₂)
  set s := Real.sqrt |l₂| * Real.sqrt |l₃| with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hss : s * s = |l₂ * l₃| := by
    calc s * s = (Real.sqrt |l₂| * Real.sqrt |l₂|) * (Real.sqrt |l₃| * Real.sqrt |l₃|) := by ring
      _ = |l₂ * l₃| := by
        rw [Real.mul_self_sqrt (abs_nonneg _), Real.mul_self_sqrt (abs_nonneg _), abs_mul]
  have hsg : s ≤ g0 V w / e ^ 2 := by
    calc s ≤ Real.sqrt (g0 V w / e ^ 2) * Real.sqrt (g0 V w / e ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt b2) (Real.sqrt_le_sqrt b3) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = g0 V w / e ^ 2 := Real.mul_self_sqrt (by positivity)
  have hm1 : |lam V w ρ L v₁| ≤ ρ⁻¹ := by
    rw [abs_of_neg hl1.2]
    linarith [hl1.1]
  have hm0 : 0 < |lam V w ρ L v₁| := abs_pos.2 hl1.2.ne
  have hinv : 1 ≤ e⁻¹ := (one_le_inv₀ he).2 he1
  have hpt : ∀ β, s * ‖FP_tI Ψ v₁ v₂ (v₁ - v₂) β‖ ≤
      4 * ρ⁻¹ * e⁻¹ * ((β v₂ : ℝ) * β (v₁ - v₂) * ‖Ψ β‖ ^ 2) ∧
      (s = 0 → FP_tI Ψ v₁ v₂ (v₁ - v₂) β = 0) := by
    intro β
    have hR : 0 ≤ 4 * ρ⁻¹ * e⁻¹ * ((β v₂ : ℝ) * β (v₁ - v₂) * ‖Ψ β‖ ^ 2) := by positivity
    unfold FP_tI
    by_cases hc0 : (a4 0 v₁ v₂ (v₁ - v₂) β).1 = 0
    · simp [FP_t, hc0, hR]
    obtain ⟨hb, h0, h1', hcoef⟩ := FP_a4_fwd h1 h2 h3 h12 h13 h23 β hc0
    unfold FP_t
    rw [hcoef]
    generalize (a4 0 v₁ v₂ (v₁ - v₂) β).2 = α at hb h0 h1' ⊢
    subst hb
    by_cases hsym : α v₁ = α (-v₁)
    · rw [ite_eq_left hsym]
      simp [hR]
    rw [ite_eq_right hsym]
    by_cases hα0 : Ψ α = 0
    · simp [hα0, hR]
    by_cases hβ0 : Ψ (softPair v₁ v₂ (v₁ - v₂) α) = 0
    · simp [hβ0]
    have hαM := FP_inM hα0
    have hβM := FP_inM hβ0
    have key := FP_termI (V := V) (w := w) hN hc α hsym hαM hβM
    have hnorm : ‖conj (Ψ α) * (FP_c v₁ v₂ (v₁ - v₂) α : ℂ) * Ψ (softPair v₁ v₂ (v₁ - v₂) α)‖ =
        ‖Ψ α‖ * FP_c v₁ v₂ (v₁ - v₂) α * ‖Ψ (softPair v₁ v₂ (v₁ - v₂) α)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (FP_c_pos v₁ v₂ _ h0 h1').le]
    rw [hnorm]
    have hb2 : (softPair v₁ v₂ (v₁ - v₂) α) v₂ = α v₂ + 1 := by
      rw [MBasic_softPair_apply]
      simp [h2, h12.symm, h23]
    have hb3 : (softPair v₁ v₂ (v₁ - v₂) α) (v₁ - v₂) = α (v₁ - v₂) + 1 := by
      rw [MBasic_softPair_apply]
      simp [h3, h13.symm, h23.symm]
    rw [hb2, hb3]
    push_cast
    set B := ‖Ψ (softPair v₁ v₂ (v₁ - v₂) α)‖
    have hx1 : (α v₁ : ℝ) ≤ 2 * e⁻¹ := by
      have hst := MStar_PL_mc hρ hαM hc.1
      have h' : (α v₁ : ℝ) ≤ (alphaStar α v₁ : ℝ) := by exact_mod_cast le_max_left _ _
      rw [hmc] at hst
      linarith
    have hn2 : (1 : ℝ) ≤ (α v₂ : ℝ) + 1 := by linarith [(Nat.cast_nonneg (α v₂) : (0 : ℝ) ≤ _)]
    have hn3 : (1 : ℝ) ≤ (α (v₁ - v₂) : ℝ) + 1 := by
      linarith [(Nat.cast_nonneg (α (v₁ - v₂)) : (0 : ℝ) ≤ _)]
    have hs2 := FP_sqrt_le hn2
    have hs3 := FP_sqrt_le hn3
    constructor
    · rw [key]
      calc 2 * |lam V w ρ L v₁| * (α v₁ : ℝ) *
            (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α (v₁ - v₂) : ℝ) + 1)) * B ^ 2
          ≤ 2 * ρ⁻¹ * (2 * e⁻¹) * (((α v₂ : ℝ) + 1) * ((α (v₁ - v₂) : ℝ) + 1)) * B ^ 2 := by
            gcongr
        _ = 4 * ρ⁻¹ * e⁻¹ * (((α v₂ : ℝ) + 1) * ((α (v₁ - v₂) : ℝ) + 1) * B ^ 2) := by ring
    · intro hs
      exfalso
      apply hβ0
      have hs' : Real.sqrt |lam V w (rhoN N) (LN N) v₂| *
          Real.sqrt |lam V w (rhoN N) (LN N) (v₁ - v₂)| = 0 := hs
      rw [hs', zero_mul] at key
      have hx1' : (0 : ℝ) < α v₁ := by exact_mod_cast h1'
      have hP : 0 < 2 * |lam V w ρ L v₁| * (α v₁ : ℝ) *
          (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α (v₁ - v₂) : ℝ) + 1)) := by
        have := Real.one_le_sqrt.2 hn2
        have := Real.one_le_sqrt.2 hn3
        positivity
      have hB : B ^ 2 = 0 := by
        rcases mul_eq_zero.1 key.symm with h | h
        · exact absurd h hP.ne'
        · exact h
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hB)
  have hsn : Summable fun β => ‖FP_t Ψ v₁ v₂ (v₁ - v₂) β‖ :=
    Expect.id4a_summable N Ψ hΨ 0 v₁ v₂ (v₁ - v₂)
  have hsI : Summable fun β => ‖FP_tI Ψ v₁ v₂ (v₁ - v₂) β‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun β => ?_) hsn
    unfold FP_tI
    split_ifs <;> simp
  have hsQ : Summable fun β : Occ => (β v₂ : ℝ) * β (v₁ - v₂) * ‖Ψ β‖ ^ 2 := by
    refine FP_summ hΨ _ ((N : ℝ) * N) (fun β hβ => ?_)
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (FP_occ_le hΨ hβ _) (FP_occ_le hΨ hβ _) (by positivity) (by positivity)
  have hQ : Expect.Q Ψ [v₂, v₁ - v₂] = ∑' β : Occ, (β v₂ : ℝ) * β (v₁ - v₂) * ‖Ψ β‖ ^ 2 := by
    simp [Expect.Q]
  have hbound : 0 ≤ 4 * C * g0 V w * ρ ^ 3 / e ^ 7 := by positivity
  by_cases hs : s = 0
  · have h0 : ∀ β, FP_tI Ψ v₁ v₂ (v₁ - v₂) β = 0 := fun β => (hpt β).2 hs
    simp [h0, hbound]
  have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hsum : s * ∑' β, ‖FP_tI Ψ v₁ v₂ (v₁ - v₂) β‖ ≤
      4 * ρ⁻¹ * e⁻¹ * Expect.Q Ψ [v₂, v₁ - v₂] := by
    rw [← tsum_mul_left, hQ, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun β => (hpt β).1) (hsI.mul_left s) (hsQ.mul_left _)
  refine (norm_tsum_le_tsum_norm hsI).trans ?_
  refine le_of_mul_le_mul_left ?_ hsp
  calc s * ∑' β, ‖FP_tI Ψ v₁ v₂ (v₁ - v₂) β‖
      ≤ 4 * ρ⁻¹ * e⁻¹ * (C * |l₂ * l₃| * ρ ^ 4 / e ^ 4) :=
        hsum.trans (mul_le_mul_of_nonneg_left h42 (by positivity))
    _ = s * (4 * C * s * ρ ^ 3 / e ^ 5) := by
        rw [← hss]
        field_simp
    _ ≤ s * (4 * C * (g0 V w / e ^ 2) * ρ ^ 3 / e ^ 5) := by gcongr
    _ = s * (4 * C * g0 V w * ρ ^ 3 / e ^ 7) := by
        field_simp

/-! ### The sums over `M_{v₁}^s` and `M_{v₁}^a`, (8.20)–(8.23) -/

/-- `α(0) α(v₁) |Ψ(α)|²` on `M_{v₁}^s`. -/
private def FP_fs (Ψ : Occ → ℂ) (v₁ : Idx) (α : Occ) : ℝ :=
  (if α v₁ = α (-v₁) then (α 0 : ℝ) * α v₁ else 0) * ‖Ψ α‖ ^ 2

/-- `α(0) α(v₁) |Ψ(α)|²` on `M_{v₁}^a`. -/
private def FP_fa (Ψ : Occ → ℂ) (v₁ : Idx) (α : Occ) : ℝ :=
  (if α v₁ = α (-v₁) then 0 else (α 0 : ℝ) * α v₁) * ‖Ψ α‖ ^ 2

/-- `α(0) α(v₁) (√((α(v₂) + 1)(α(v₃) + 1)) - 1) |Ψ(α)|²` on `M_{v₁}^s`, the summand of `A₂`
in (8.20). -/
private def FP_fr (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) (α : Occ) : ℝ :=
  (if α v₁ = α (-v₁) then (α 0 : ℝ) * α v₁ *
    (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α v₃ : ℝ) + 1) - 1) else 0) * ‖Ψ α‖ ^ 2

/-- `0 ≤ √(a + 1) √(b + 1) - 1 ≤ a + b` for `a, b ≥ 0`. -/
private theorem FP_sqrt_facts {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Real.sqrt (a + 1) * Real.sqrt (b + 1) - 1 ∧
      Real.sqrt (a + 1) * Real.sqrt (b + 1) - 1 ≤ a + b := by
  have s2 := Real.one_le_sqrt.2 (by linarith : (1 : ℝ) ≤ a + 1)
  have s3 := Real.one_le_sqrt.2 (by linarith : (1 : ℝ) ≤ b + 1)
  have q2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ a + 1)
  have q3 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b + 1)
  have hss : 1 ≤ Real.sqrt (a + 1) * Real.sqrt (b + 1) := one_le_mul_of_one_le_of_one_le s2 s3
  refine ⟨by linarith, ?_⟩
  nlinarith [sq_nonneg (Real.sqrt (a + 1) - Real.sqrt (b + 1))]

private theorem FP_sums {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ : Idx) :
    Summable (FP_fs Ψ v₁) ∧ Summable (FP_fa Ψ v₁) ∧ Summable (FP_fr Ψ v₁ v₂ v₃) ∧
      ∑' α, FP_h Ψ v₁ v₂ v₃ α = (∑' α, FP_fs Ψ v₁ α) + ∑' α, FP_fr Ψ v₁ v₂ v₃ α ∧
      Expect.Q Ψ [0, v₁] = (∑' α, FP_fs Ψ v₁ α) + ∑' α, FP_fa Ψ v₁ α := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsfs : Summable (FP_fs Ψ v₁) := by
    refine FP_summ hΨ _ ((N : ℝ) * N) (fun α hα => ?_)
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (FP_occ_le hΨ hα _) (FP_occ_le hΨ hα _) (by positivity) hN0
    · simp only [abs_zero]
      positivity
  have hsfa : Summable (FP_fa Ψ v₁) := by
    refine FP_summ hΨ _ ((N : ℝ) * N) (fun α hα => ?_)
    split_ifs
    · simp only [abs_zero]
      positivity
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (FP_occ_le hΨ hα _) (FP_occ_le hΨ hα _) (by positivity) hN0
  have hsh : Summable (FP_h Ψ v₁ v₂ v₃) := by
    refine FP_summ hΨ _ ((N : ℝ) * N * (((N : ℝ) + 1) * ((N : ℝ) + 1))) (fun α hα => ?_)
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      have a2 := FP_sqrt_le (by linarith [(Nat.cast_nonneg (α v₂) : (0 : ℝ) ≤ _)] :
        (1 : ℝ) ≤ (α v₂ : ℝ) + 1)
      have a3 := FP_sqrt_le (by linarith [(Nat.cast_nonneg (α v₃) : (0 : ℝ) ≤ _)] :
        (1 : ℝ) ≤ (α v₃ : ℝ) + 1)
      have c2 := FP_occ_le hΨ hα v₂
      have c3 := FP_occ_le hΨ hα v₃
      have c0 := FP_occ_le hΨ hα 0
      have c1 := FP_occ_le hΨ hα v₁
      have d2 : Real.sqrt ((α v₂ : ℝ) + 1) ≤ (N : ℝ) + 1 := by linarith
      have d3 : Real.sqrt ((α v₃ : ℝ) + 1) ≤ (N : ℝ) + 1 := by linarith
      gcongr
    · simp only [abs_zero]
      positivity
  have hfr_eq : ∀ α, FP_fr Ψ v₁ v₂ v₃ α = FP_h Ψ v₁ v₂ v₃ α - FP_fs Ψ v₁ α := by
    intro α
    simp only [FP_fr, FP_h, FP_fs]
    split_ifs <;> ring
  have hsfr : Summable (FP_fr Ψ v₁ v₂ v₃) := by
    have : FP_fr Ψ v₁ v₂ v₃ = fun α => FP_h Ψ v₁ v₂ v₃ α - FP_fs Ψ v₁ α := funext hfr_eq
    rw [this]
    exact hsh.sub hsfs
  refine ⟨hsfs, hsfa, hsfr, ?_, ?_⟩
  · rw [tsum_congr hfr_eq, hsh.tsum_sub hsfs]
    ring
  · rw [← hsfs.tsum_add hsfa]
    simp only [Expect.Q, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    refine tsum_congr (fun α => ?_)
    simp only [FP_fs, FP_fa]
    split_ifs <;> ring

private theorem FP_sums_nonneg (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) :
    0 ≤ ∑' α, FP_fs Ψ v₁ α ∧ 0 ≤ ∑' α, FP_fa Ψ v₁ α ∧ 0 ≤ ∑' α, FP_fr Ψ v₁ v₂ v₃ α := by
  refine ⟨tsum_nonneg (fun α => ?_), tsum_nonneg (fun α => ?_), tsum_nonneg (fun α => ?_)⟩
  · simp only [FP_fs]
    split_ifs <;> positivity
  · simp only [FP_fa]
    split_ifs <;> positivity
  · simp only [FP_fr]
    split_ifs
    · have := (FP_sqrt_facts (Nat.cast_nonneg (α v₂)) (Nat.cast_nonneg (α v₃))).1
      positivity
    · simp

private theorem FP_Q_one (Ψ : Occ → ℂ) (u : Idx) :
    Expect.Q Ψ [u] = ∑' α : Occ, (α u : ℝ) * ‖Ψ α‖ ^ 2 := by
  simp [Expect.Q]

private theorem FP_sq {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (u : Idx) :
    Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 :=
  FP_summ hΨ _ (N : ℝ) (fun α hα => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact FP_occ_le hΨ hα u)

/-- (8.20)–(8.21): `A₂ ≤ N K (Q_Ψ(v₂) + Q_Ψ(v₃))` when `α(0) ≤ N` and `α(v₁) ≤ K` on the
support of `Ψ`. -/
private theorem FP_fr_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ : Idx) {K : ℝ}
    (hocc : ∀ α, Ψ α ≠ 0 → (α 0 : ℝ) ≤ N ∧ (α v₁ : ℝ) ≤ K) (hK : 0 ≤ K) :
    ∑' α, FP_fr Ψ v₁ v₂ v₃ α ≤ (N : ℝ) * K * (Expect.Q Ψ [v₂] + Expect.Q Ψ [v₃]) := by
  rw [FP_Q_one, FP_Q_one, ← (FP_sq hΨ v₂).tsum_add (FP_sq hΨ v₃), ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun α => ?_) (FP_sums hΨ v₁ v₂ v₃).2.2.1
    (((FP_sq hΨ v₂).add (FP_sq hΨ v₃)).mul_left _)
  by_cases hα : Ψ α = 0
  · simp [FP_fr, hα]
  obtain ⟨c0, c1⟩ := hocc α hα
  simp only [FP_fr]
  split_ifs
  · obtain ⟨hk0, hk⟩ := FP_sqrt_facts (Nat.cast_nonneg (α v₂)) (Nat.cast_nonneg (α v₃))
    calc (α 0 : ℝ) * α v₁ *
          (Real.sqrt ((α v₂ : ℝ) + 1) * Real.sqrt ((α v₃ : ℝ) + 1) - 1) * ‖Ψ α‖ ^ 2
        ≤ (N : ℝ) * K * ((α v₂ : ℝ) + α v₃) * ‖Ψ α‖ ^ 2 := by gcongr
      _ = (N : ℝ) * K * ((α v₂ : ℝ) * ‖Ψ α‖ ^ 2 + (α v₃ : ℝ) * ‖Ψ α‖ ^ 2) := by ring
  · simp only [zero_mul]
    positivity

/-- (8.22)–(8.23): `Σ_{M_{v₁}^a} α(0) α(v₁) |Ψ(α)|² ≤ N K Σ_{α ∈ P} |Ψ(α)|²` when the support
of `Ψ` off `M_{v₁}^s` lies in `P`. -/
private theorem FP_fa_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ : Idx) {K : ℝ}
    (hocc : ∀ α, Ψ α ≠ 0 → (α 0 : ℝ) ≤ N ∧ (α v₁ : ℝ) ≤ K) (hK : 0 ≤ K) (P : Occ → Prop)
    (hP : ∀ α, Ψ α ≠ 0 → α v₁ ≠ α (-v₁) → P α) :
    ∑' α, FP_fa Ψ v₁ α ≤ (N : ℝ) * K * ∑' α : Occ, (if P α then ‖Ψ α‖ ^ 2 else 0) := by
  have hsP : Summable fun α : Occ => if P α then ‖Ψ α‖ ^ 2 else 0 := by
    refine Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) hΨ.1.summable
    · split_ifs <;> positivity
    · split_ifs <;> simp
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun α => ?_) (FP_sums hΨ v₁ v₁ v₁).2.1 (hsP.mul_left _)
  by_cases hα : Ψ α = 0
  · simp [FP_fa, hα]
  obtain ⟨c0, c1⟩ := hocc α hα
  simp only [FP_fa]
  by_cases hsym : α v₁ = α (-v₁)
  · rw [ite_eq_left hsym, zero_mul]
    split_ifs <;> positivity
  · rw [ite_eq_right hsym, ite_eq_left (hP α hα hsym)]
    gcongr

/-- `Q_Ψ(0, v₁) ≤ N Q_Ψ(v₁)` for an `N`-particle state. -/
private theorem FP_Q01_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ : Idx) :
    Expect.Q Ψ [0, v₁] ≤ (N : ℝ) * Expect.Q Ψ [v₁] := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [FP_Q_one, ← tsum_mul_left]
  simp only [Expect.Q, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  refine Summable.tsum_le_tsum (fun α => ?_) ?_ ((FP_sq hΨ v₁).mul_left _)
  · by_cases hα : Ψ α = 0
    · simp [hα]
    have c0 := FP_occ_le hΨ hα 0
    calc (α 0 : ℝ) * α v₁ * ‖Ψ α‖ ^ 2 ≤ (N : ℝ) * α v₁ * ‖Ψ α‖ ^ 2 := by gcongr
      _ = (N : ℝ) * ((α v₁ : ℝ) * ‖Ψ α‖ ^ 2) := by ring
  · exact FP_summ hΨ _ ((N : ℝ) * N) (fun α hα => by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (FP_occ_le hΨ hα _) (FP_occ_le hΨ hα _) (by positivity) hN0)

/-! ### Assembly of (8.24)–(8.26) -/

/-- The factor `D = 2 csqrt(λ_{v₂}) csqrt(λ_{v₃}) / |Λ|`: `|D| ≤ 2g/(|Λ| ε²)` and
`|D - 2λ_{v₂}/|Λ|| ≤ 4r/|Λ|` when `|λ_{v₂}|, |λ_{v₃}| ≤ g/ε²` and `|λ_{v₂} - λ_{v₃}| ≤ r`. -/
private theorem FP_D {l₂ l₃ L3 g e r : ℝ} (hL3 : 0 < L3) (b2 : |l₂| ≤ g / e ^ 2)
    (b3 : |l₃| ≤ g / e ^ 2) (hsub : |l₂ - l₃| ≤ r) :
    ‖((2 / L3 : ℝ) : ℂ) * (csqrt l₂ * csqrt l₃)‖ ≤ 2 / L3 * (g / e ^ 2) ∧
      ‖((2 / L3 : ℝ) : ℂ) * (csqrt l₂ * csqrt l₃) - ((2 * l₂ / L3 : ℝ) : ℂ)‖ ≤
        2 / L3 * (2 * r) := by
  have hg : 0 ≤ g / e ^ 2 := (abs_nonneg _).trans b2
  constructor
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / L3), FP_norm_csqrt, FP_norm_csqrt]
    gcongr
    calc Real.sqrt |l₂| * Real.sqrt |l₃| ≤ Real.sqrt (g / e ^ 2) * Real.sqrt (g / e ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt b2) (Real.sqrt_le_sqrt b3) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = g / e ^ 2 := Real.mul_self_sqrt hg
  · have e : ((2 / L3 : ℝ) : ℂ) * (csqrt l₂ * csqrt l₃) - ((2 * l₂ / L3 : ℝ) : ℂ) =
        ((2 / L3 : ℝ) : ℂ) * (csqrt l₂ * csqrt l₃ - l₂) := by
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / L3)]
    gcongr
    exact (OneLeg_csqrt_mul_sub l₂ l₃).trans (by linarith)

/-- The exponent rows of (8.17)–(8.26) for one pair, as an inequality between real numbers. -/
private theorem FP_arith {ρ e L3 g N C42 C54 C23 r X d d' Fr Fa Ma Q01 Q1 Q2 Q3 : ℝ}
    (hρ : 0 < ρ) (he : 0 < e) (hρe : ρ ≤ e ^ 2) (hL3 : 0 < L3) (hg : 0 ≤ g)
    (hC42 : 0 ≤ C42) (hC54 : 0 ≤ C54) (hNL : N = ρ * L3)
    (hX : X ≤ 4 * C42 * g * ρ ^ 3 / e ^ 7) (hd : d ≤ 2 / L3 * (g / e ^ 2))
    (hd' : d' ≤ 2 / L3 * (2 * r)) (hr0 : 0 ≤ r) (hFr0 : 0 ≤ Fr)
    (hFr : Fr ≤ N * (2 * e⁻¹) * (Q2 + Q3))
    (hQ2 : Q2 ≤ C54 * g * ρ ^ 2 / e ^ 4) (hQ3 : Q3 ≤ C54 * g * ρ ^ 2 / e ^ 4)
    (hFa0 : 0 ≤ Fa) (hFa : Fa ≤ N * (2 * e⁻¹) * Ma) (hMa : Ma ≤ C23 * ρ * e⁻¹ / e)
    (hQ0 : 0 ≤ Q01) (hQ : Q01 ≤ N * Q1) :
    X + d * Fr + d * Fa + d' * Q01 ≤
      (4 * C42 * g + 8 * C54 * g ^ 2 + 4 * C23 * g) * (ρ ^ 2 / e ^ 5) + 4 * (r * ρ) * Q1 := by
  have hN : 0 ≤ N := by rw [hNL]; positivity
  have hA : d * Fr ≤ 8 * C54 * g ^ 2 * ρ ^ 3 / e ^ 7 := by
    calc d * Fr ≤ 2 / L3 * (g / e ^ 2) * (N * (2 * e⁻¹) *
          (C54 * g * ρ ^ 2 / e ^ 4 + C54 * g * ρ ^ 2 / e ^ 4)) := by
          gcongr
          exact hFr.trans (by gcongr)
      _ = 8 * C54 * g ^ 2 * ρ ^ 3 / e ^ 7 := by
          rw [hNL]
          field_simp
          ring
  have hB : d * Fa ≤ 4 * C23 * g * ρ ^ 2 / e ^ 5 := by
    calc d * Fa ≤ 2 / L3 * (g / e ^ 2) * (N * (2 * e⁻¹) * (C23 * ρ * e⁻¹ / e)) := by
          gcongr
          exact hFa.trans (by gcongr)
      _ = 4 * C23 * g * ρ ^ 2 / e ^ 5 := by
          rw [hNL]
          field_simp
          ring
  have hC : d' * Q01 ≤ 4 * (r * ρ) * Q1 := by
    calc d' * Q01 ≤ 2 / L3 * (2 * r) * (N * Q1) := by gcongr
      _ = 4 * (r * ρ) * Q1 := by
          rw [hNL]
          field_simp
          ring
  have hk : ρ ^ 3 / e ^ 7 ≤ ρ ^ 2 / e ^ 5 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ρ ^ 3 * e ^ 5 = (ρ ^ 2 * e ^ 5) * ρ := by ring
    have h2 : ρ ^ 2 * e ^ 7 = (ρ ^ 2 * e ^ 5) * e ^ 2 := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hρe (by positivity)
  have hk1 : 4 * C42 * g * ρ ^ 3 / e ^ 7 ≤ 4 * C42 * g * (ρ ^ 2 / e ^ 5) := by
    rw [mul_div_assoc]
    gcongr
  have hk2 : 8 * C54 * g ^ 2 * ρ ^ 3 / e ^ 7 ≤ 8 * C54 * g ^ 2 * (ρ ^ 2 / e ^ 5) := by
    rw [mul_div_assoc]
    gcongr
  have hk3 : 4 * C23 * g * ρ ^ 2 / e ^ 5 = 4 * C23 * g * (ρ ^ 2 / e ^ 5) := by ring
  have hsum : (4 * C42 * g + 8 * C54 * g ^ 2 + 4 * C23 * g) * (ρ ^ 2 / e ^ 5) =
      4 * C42 * g * (ρ ^ 2 / e ^ 5) + 8 * C54 * g ^ 2 * (ρ ^ 2 / e ^ 5) +
        4 * C23 * g * (ρ ^ 2 / e ^ 5) := by ring
  linarith

/-- `C ρ² |λ| / |p|² ≤ C g ρ² ε⁻⁴` for `|λ| ≤ g/ε²` and `ε < |p|`. -/
private theorem FP_Qb {C ρ l g e p : ℝ} (hC : 0 ≤ C) (he : 0 < e) (b : |l| ≤ g / e ^ 2)
    (hp : e < p) : C * ρ ^ 2 * |l| / p ^ 2 ≤ C * g * ρ ^ 2 / e ^ 4 := by
  have hp0 : 0 < p := he.trans hp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : e ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ he.le hp.le 2
  have hb : |l| * e ^ 2 ≤ g := by
    have := (le_div_iff₀ (by positivity)).1 b
    linarith
  have hg : 0 ≤ g := le_trans (by positivity) hb
  calc C * ρ ^ 2 * |l| * e ^ 4 = C * ρ ^ 2 * (|l| * e ^ 2) * e ^ 2 := by ring
    _ ≤ C * ρ ^ 2 * g * p ^ 2 := by gcongr
    _ = C * g * ρ ^ 2 * p ^ 2 := by ring

/-- (8.17)–(8.26) for one pair in case (8.2) at a fixed `N ≥ 1`, from the bounds (5.42)
[boundpsifixeduv], (5.15) [ubpsiuroughPH], (5.23) [boundMa] and (8.25) at that `N`. -/
private theorem FP_main {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {v₁ v₂ : Idx} (hc : OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂)
    {C42 C54 C23 : ℝ} (hC42 : 0 ≤ C42) (hC54 : 0 ≤ C54)
    (h42 : Expect.Q (trialState V w kc N) [v₂, v₁ - v₂] ≤
      C42 * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) (v₁ - v₂)| * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4)
    (h54 : ∀ u : Idx, inPH (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        C54 * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2)
    (h23 : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N v₁ α then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C23 * rhoN N * mc (rhoN N) / epsP (rhoN N))
    (hsub : |lam V w (rhoN N) (LN N) v₂ - lam V w (rhoN N) (LN N) (v₁ - v₂)| ≤
      rhoN N ^ (1/3 : ℝ)) :
    ‖OneLeg_expA (trialState V w kc N) v₁ v₂ (v₁ - v₂) -
        ((2 * lam V w (rhoN N) (LN N) v₂ * Expect.Q (trialState V w kc N) [0, v₁] /
          LN N ^ 3 : ℝ) : ℂ)‖ ≤
      (4 * C42 * g0 V w + 8 * C54 * g0 V w ^ 2 + 4 * C23 * g0 V w) * rhoN N ^ (2 - 1/40 : ℝ) +
        4 * rhoN N ^ (4/3 : ℝ) * Expect.Q (trialState V w kc N) [v₁] := by
  have hI := FP_partI hV hw hN hc hC42 h42
  rw [FP_split hN hc]
  obtain ⟨hNρ, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  obtain ⟨-, -, -, hH, hQ01⟩ := FP_sums hΨ v₁ v₂ (v₁ - v₂)
  obtain ⟨hfs0, hfa0, hfr0⟩ := FP_sums_nonneg (trialState V w kc N) v₁ v₂ (v₁ - v₂)
  have he : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have he1 : epsP (rhoN N) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hmc : mc (rhoN N) = (epsP (rhoN N))⁻¹ := by rw [mc, epsP, Real.rpow_neg hρ.le]
  have hocc : ∀ α, trialState V w kc N α ≠ 0 →
      (α 0 : ℝ) ≤ N ∧ (α v₁ : ℝ) ≤ 2 * (epsP (rhoN N))⁻¹ := by
    intro α hα
    refine ⟨FP_occ_le hΨ hα 0, ?_⟩
    have hst := MStar_PL_mc hρ (FP_inM hα) hc.1
    have h' : (α v₁ : ℝ) ≤ (alphaStar α v₁ : ℝ) := by exact_mod_cast le_max_left _ _
    have hinv : 1 ≤ (epsP (rhoN N))⁻¹ := (one_le_inv₀ he).2 he1
    rw [hmc] at hst
    linarith
  have hK : 0 ≤ 2 * (epsP (rhoN N))⁻¹ := by positivity
  have hFr := FP_fr_le hΨ v₁ v₂ (v₁ - v₂) hocc hK
  have hFa := FP_fa_le hΨ v₁ hocc hK (InMuA (rhoN N) (LN N) kc N v₁)
    (fun α hα hs => ⟨FP_inM hα, hs⟩)
  have hQ := FP_Q01_le hΨ v₁
  have hg := scat_g0_pos hV hw
  have b2 := scat_lam_PH hV hw (rhoN N) hρ (LN N) v₂ hc.2.1.1
  have b3 := scat_lam_PH hV hw (rhoN N) hρ (LN N) (v₁ - v₂) hc.2.2.1
  have hL3 : (0 : ℝ) < LN N ^ 3 := by positivity
  obtain ⟨hD, hDc⟩ := FP_D hL3 b2 b3 hsub
  have hQ2 := (h54 v₂ hc.2.1.1).trans (FP_Qb hC54 he b2 hc.2.1.1)
  have hQ3 := (h54 (v₁ - v₂) hc.2.2.1).trans (FP_Qb hC54 he b3 hc.2.2.1)
  have hQ0 : 0 ≤ Expect.Q (trialState V w kc N) [0, v₁] := by
    rw [hQ01]
    linarith
  rw [hmc] at h23
  have hρe : rhoN N ≤ epsP (rhoN N) ^ 2 := by
    have e2 : epsP (rhoN N) ^ 2 = rhoN N ^ (1 / 100 : ℝ) := by
      rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    rw [e2]
    exact Real.self_le_rpow_of_le_one hρ.le hρ1 (by norm_num)
  have hpow : rhoN N ^ (2 - 1/40 : ℝ) = rhoN N ^ 2 / epsP (rhoN N) ^ 5 := by
    have e5 : epsP (rhoN N) ^ 5 = rhoN N ^ (1 / 40 : ℝ) := by
      rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    rw [Real.rpow_sub hρ, e5, Real.rpow_two]
  have hpow' : rhoN N ^ (4/3 : ℝ) = rhoN N ^ (1/3 : ℝ) * rhoN N := by
    rw [← Real.rpow_add_one hρ.ne']
    norm_num
  set SI := ∑' β, FP_tI (trialState V w kc N) v₁ v₂ (v₁ - v₂) β
  set D : ℂ := ((2 / LN N ^ 3 : ℝ) : ℂ) * (csqrt (lam V w (rhoN N) (LN N) v₂) *
    csqrt (lam V w (rhoN N) (LN N) (v₁ - v₂))) with hDdef
  set c : ℝ := 2 * lam V w (rhoN N) (LN N) v₂ / LN N ^ 3
  set Q01 := Expect.Q (trialState V w kc N) [0, v₁]
  set Fs := ∑' α, FP_fs (trialState V w kc N) v₁ α
  set Fa := ∑' α, FP_fa (trialState V w kc N) v₁ α
  set Fr := ∑' α, FP_fr (trialState V w kc N) v₁ v₂ (v₁ - v₂) α
  have e1 : (2 * lam V w (rhoN N) (LN N) v₂ * Q01 / LN N ^ 3 : ℝ) = c * Q01 := by ring
  rw [e1, hH]
  have hdec : SI + D * ((Fs + Fr : ℝ) : ℂ) - ((c * Q01 : ℝ) : ℂ) =
      SI + D * (Fr : ℂ) - D * (Fa : ℂ) + (D - (c : ℂ)) * (Q01 : ℂ) := by
    rw [hQ01]
    push_cast
    ring
  rw [hdec, hpow, hpow']
  have htri : ‖SI + D * (Fr : ℂ) + -(D * (Fa : ℂ)) + (D - (c : ℂ)) * (Q01 : ℂ)‖ ≤
      ‖SI‖ + ‖D * (Fr : ℂ)‖ + ‖-(D * (Fa : ℂ))‖ + ‖(D - (c : ℂ)) * (Q01 : ℂ)‖ := norm_add₄_le
  rw [norm_neg, ← sub_eq_add_neg, norm_mul D (Fr : ℂ), norm_mul D (Fa : ℂ),
    norm_mul (D - (c : ℂ)) (Q01 : ℂ), Complex.norm_real Fr, Complex.norm_real Fa,
    Complex.norm_real Q01, Real.norm_eq_abs Fr, Real.norm_eq_abs Fa, Real.norm_eq_abs Q01,
    abs_of_nonneg hfr0, abs_of_nonneg hfa0, abs_of_nonneg hQ0] at htri
  refine htri.trans ?_
  exact FP_arith hρ he hρe hL3 hg.le hC42 hC54 hNρ.symm hI hD hDc
    (Real.rpow_nonneg hρ.le _) hfr0 hFr hQ2 hQ3 hfa0 hFa h23 hQ0 hQ

/-- (8.17)–(8.26) for one pair in case (8.2) [one0firstcase]:
`⟨a†_0 a†_{v₁} a_{v₂} a_{v₃}⟩_Ψ = 2λ_{v₂} Q_Ψ(0, v₁)/|Λ|` up to
`Cρ^{2-1/40} + 4ρ^{4/3} Q_Ψ(v₁)`. -/
theorem OneLeg_pair_first {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ v₁ v₂ : Idx,
      OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂ →
      ‖OneLeg_expA (trialState V w kc N) v₁ v₂ (v₁ - v₂) -
          ((2 * lam V w (rhoN N) (LN N) v₂ * Expect.Q (trialState V w kc N) [0, v₁] /
            LN N ^ 3 : ℝ) : ℂ)‖ ≤
        C * rhoN N ^ (2 - 1/40 : ℝ) +
          4 * rhoN N ^ (4/3 : ℝ) * Expect.Q (trialState V w kc N) [v₁] := by
  obtain ⟨C42, hC42, N42, h42⟩ := Eq5_42 V w
  obtain ⟨C54, hC54, N54, h54⟩ := Lemma5_4_PH V w
  obtain ⟨C23, hC23, N23, h23⟩ := Eq5_23 V w
  obtain ⟨Nl, hl⟩ := OneLeg_lam_sub hV hw
  have hg := (scat_g0_pos hV hw).le
  refine ⟨4 * C42 * g0 V w + 8 * C54 * g0 V w ^ 2 + 4 * C23 * g0 V w, by positivity,
    max (max N42 N54) (max (max N23 Nl) 1), fun N hN kc v₁ v₂ hc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN42, hN54⟩, ⟨hN23, hNl⟩, hN1⟩ := hN
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  obtain ⟨h1, -, -, -, -, h23'⟩ := FP_legs hρ hc
  have hs : v₂ + (v₁ - v₂) = v₁ := add_sub_cancel v₂ v₁
  refine FP_main hV hw hN1 hc hC42 hC54
    (h42 N hN42 kc v₂ (v₁ - v₂) hc.2.1.1 hc.2.2.1 h23' (by rw [hs]; exact h1))
    (fun u hu => h54 N hN54 kc u hu) (h23 N hN23 kc v₁ hc.1)
    (hl N hNl v₂ (v₁ - v₂) hc.2.1.1 hc.2.2.1 (by rw [hs]; exact hc.1))

end LHYUpper
