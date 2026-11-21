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

/-! ### Auxiliary facts on `M`, on `Ψ` and on nonnegative series -/

private lemma Ratio_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _

private lemma Ratio_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hM
  exact h (by simp [trialState, hM])

private lemma Ratio_trial_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} {α : Occ}
    (h : InM (rhoN N) (LN N) kc N α) :
    trialState V w kc N α = (CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) α := by
  rw [FIdentities_trialState]
  simp [h]

private lemma Ratio_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt h', abs_of_neg (not_le.1 h)]

private lemma Ratio_trial_zero (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {γ : Occ} {v : Idx}
    (hv : v ≠ 0) (hl : lam V w (rhoN N) (LN N) v = 0) (hγ : 1 ≤ γ v) :
    trialState V w kc N γ = 0 := by
  rw [FIdentities_trialState]
  split_ifs
  · have : f0 V w (rhoN N) (LN N) γ = 0 := by
      unfold f0
      rw [Finset.prod_eq_zero (i := v) ?_ ?_]
      · simp
      · simp only [Finset.mem_filter, Finsupp.mem_support_iff]
        exact ⟨by omega, hv⟩
      · rw [hl]
        simp only [csqrt, le_refl, ite_true, Real.sqrt_zero, Complex.ofReal_zero]
        exact zero_pow (by omega)
    rw [this, mul_zero]
  · rfl

private lemma Ratio_a4_apply {v₁ v₂ v₃ : Idx} {β : Occ} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃)
    (hne : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) :
    (a4 0 v₁ v₂ v₃ β).2 0 = β 0 + 1 ∧ (a4 0 v₁ v₂ v₃ β).2 v₁ = β v₁ + 1 ∧
      (a4 0 v₁ v₂ v₃ β).2 v₂ + 1 = β v₂ ∧ (a4 0 v₁ v₂ v₃ β).2 v₃ + 1 = β v₃ := by
  obtain ⟨β', rfl⟩ := a4_exists_add 0 v₁ v₂ v₃ β hne
  rw [a4_of_add]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  simp [h₁, h₂, h₃, h₁₂, h₁₃, h₂₃, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₁₂,
    Ne.symm h₁₃, Ne.symm h₂₃]

private lemma Ratio_c_sq {v₁ v₂ v₃ : Idx} (β : Occ) (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    (a4 0 v₁ v₂ v₃ β).1 ^ 2 = (β v₃ : ℝ) * β v₂ * (β v₁ + 1) * (β 0 + 1) := by
  rw [a4_fst_sq]
  simp [h₁₂, h₁₃, h₂₃, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃]

/-- Reindexing `β ↦ T(β)` on `{c(β) ≠ 0}`. -/
private lemma Ratio_reindex (u₁ u₂ u₃ u₄ : Idx) {h : Occ → ℝ} (h0 : ∀ γ, 0 ≤ h γ)
    (hs : Summable h) :
    Summable (fun β => if (a4 u₁ u₂ u₃ u₄ β).1 ≠ 0 then h (a4 u₁ u₂ u₃ u₄ β).2 else 0) ∧
      (∑' β, if (a4 u₁ u₂ u₃ u₄ β).1 ≠ 0 then h (a4 u₁ u₂ u₃ u₄ β).2 else 0) ≤ ∑' γ, h γ := by
  have hnn : 0 ≤ fun β => if (a4 u₁ u₂ u₃ u₄ β).1 ≠ 0 then h (a4 u₁ u₂ u₃ u₄ β).2 else 0 :=
    fun β => by dsimp only; split_ifs <;> simp [h0]
  have key : ∀ s : Finset Occ,
      ∑ β ∈ s, (if (a4 u₁ u₂ u₃ u₄ β).1 ≠ 0 then h (a4 u₁ u₂ u₃ u₄ β).2 else 0) ≤
        ∑' γ, h γ := by
    intro s
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hinj : Set.InjOn (fun β => (a4 u₁ u₂ u₃ u₄ β).2)
        ↑(s.filter fun β => (a4 u₁ u₂ u₃ u₄ β).1 ≠ 0) :=
      (a4_injOn u₁ u₂ u₃ u₄).mono fun x hx => (Finset.mem_filter.1 hx).2
    rw [← Finset.sum_image (f := h) hinj]
    exact hs.sum_le_tsum _ (fun i _ => h0 i)
  exact ⟨summable_of_sum_le hnn key, Real.tsum_le_of_sum_le hnn key⟩

/-- A weight bounded on the support of an `N`-particle state is summable against `|Ψ|²`. -/
private lemma Ratio_summable_w {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (k : Occ → ℝ) (K : ℝ)
    (hk : ∀ γ, γ.num = N → |k γ| ≤ K) : Summable fun γ => k γ * ‖Ψ γ‖ ^ 2 := by
  have hK : 0 ≤ K := by
    have := hk (Finsupp.single 0 N) (by simp [Occ.num, Finsupp.sum_single_index])
    exact (abs_nonneg _).trans this
  refine Summable.of_norm_bounded (hΨ.1.summable.mul_left K) fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg (Ψ γ)) 2)]
  by_cases h : Ψ γ = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_right (hk γ (hΨ.2 γ h)) (by positivity)

private lemma Ratio_Q1 (Ψ : Occ → ℂ) (u : Idx) :
    Expect.Q Ψ [u] = ∑' γ, (γ u : ℝ) * ‖Ψ γ‖ ^ 2 := by
  simp [Expect.Q]

private lemma Ratio_Q2 (Ψ : Occ → ℂ) (u v : Idx) :
    Expect.Q Ψ [u, v] = ∑' γ, (γ u : ℝ) * γ v * ‖Ψ γ‖ ^ 2 := by
  simp [Expect.Q]

/-! ### Powers of `ρ` and the eventual bounds of (5.10) -/

/-- `ρ^{k/200} = ε^k`, (3.2) [defepseta]. -/
private lemma Ratio_rpow_eps {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ} (hx : x = (k : ℝ) / 200) :
    ρ ^ x = epsP ρ ^ k := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ, hx]
  ring_nf

private lemma Ratio_rpow_eps_neg {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ}
    (hx : x = -((k : ℝ) / 200)) : ρ ^ x = (epsP ρ ^ k)⁻¹ := by
  rw [hx, Real.rpow_neg hρ, Ratio_rpow_eps hρ k rfl]

/-- `m_c = ε⁻¹`, (3.8) [defmc]. -/
private lemma Ratio_mc {ρ : ℝ} (hρ : 0 ≤ ρ) : mc ρ = (epsP ρ)⁻¹ := by
  rw [mc, Ratio_rpow_eps_neg hρ 1 (by norm_num), pow_one]

private lemma Ratio_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := 8 / 17 * a) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

private lemma Ratio_ev_eps {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, epsP (rhoN N) ≤ δ :=
  ((Ratio_tendsto_rpow (a := 1 / 200) (by norm_num)).eventually_lt_const hδ).mono
    fun _ h => h.le

private lemma Ratio_tendsto_rho : Tendsto rhoN atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using Ratio_tendsto_rpow (a := 1) one_pos
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Particles_rhoN_LN hN).2.1

/-- (5.10) at `ρ = ρ_N`, for all large `N`. -/
private lemma Ratio_ev_lam {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ᶠ N : ℕ in atTop, ∀ (L : ℝ) (n : Idx), inPL (rhoN N) L n →
      lam V w (rhoN N) L n ≤ -(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ :=
  Ratio_tendsto_rho.eventually (scat_lam_PL_le hV hw)

/-- `c ≤ -ρ λ_u ≤ 1` on `P_L` with `c = g₀ ε² / 2`, (5.10). -/
private lemma Ratio_hlam {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    {N : ℕ} (hN : 1 ≤ N)
    (hl : ∀ (L : ℝ) (n : Idx), inPL (rhoN N) L n →
      lam V w (rhoN N) L n ≤ -(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹)
    (u : Idx) (hu : inPL (rhoN N) (LN N) u) :
    g0 V w / 2 * epsP (rhoN N) ^ 2 ≤ -(rhoN N * lam V w (rhoN N) (LN N) u) ∧
      -(rhoN N * lam V w (rhoN N) (LN N) u) ≤ 1 := by
  have hρ := (Particles_rhoN_LN hN).2.1
  have h1 := hl _ u hu
  have h2 := scat_lam_PL hV hw _ hρ _ u hu
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [show rhoN N * (-(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) =
      -(g0 V w / 2 * epsP (rhoN N) ^ 2) by field_simp] at this
    linarith
  · have := mul_lt_mul_of_pos_left h2.1 hρ
    rw [show rhoN N * -(rhoN N)⁻¹ = -1 by field_simp] at this
    linarith

/-- The constant `K³` of the ratio bound is at most `ρ^{-1/10}` once `ε ≤ min (1/2) (2g)³`. -/
private lemma Ratio_K3 {ρ g : ℝ} (hρ : 0 < ρ) (hg : 0 < g) (ht : epsP ρ ≤ 1 / 2)
    (ht' : epsP ρ ≤ (2 * g) ^ 3) :
    max (4 * (mc ρ + 1)) (1 / (4 * (g / 2 * epsP ρ ^ 2))) ^ 3 ≤ ρ ^ (-(1 / 10 : ℝ)) := by
  rw [Ratio_mc hρ.le, Ratio_rpow_eps_neg hρ.le 20 (by norm_num)]
  set t := epsP ρ with ht_def
  have t0 : 0 < t := by rw [ht_def, epsP]; positivity
  have t1 : t ≤ 1 := ht.trans (by norm_num)
  rw [show (t ^ 20)⁻¹ = 1 / t ^ 20 from (one_div _).symm, le_div_iff₀ (by positivity)]
  rcases le_total (4 * (t⁻¹ + 1)) (1 / (4 * (g / 2 * t ^ 2))) with h | h
  · rw [max_eq_right h]
    have e : (1 / (4 * (g / 2 * t ^ 2))) ^ 3 * t ^ 20 = t ^ 14 / (2 * g) ^ 3 := by
      field_simp
      ring
    rw [e, div_le_one (by positivity)]
    calc t ^ 14 ≤ t ^ 1 := pow_le_pow_of_le_one t0.le t1 (by norm_num)
      _ = t := pow_one t
      _ ≤ (2 * g) ^ 3 := ht'
  · rw [max_eq_left h]
    have e : (4 * (t⁻¹ + 1)) ^ 3 * t ^ 20 = (4 * (1 + t)) ^ 3 * t ^ 17 := by
      field_simp
    rw [e]
    have h1 : (4 * (1 + t)) ^ 3 ≤ 216 := by
      have : 4 * (1 + t) ≤ 6 := by linarith
      calc (4 * (1 + t)) ^ 3 ≤ 6 ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = 216 := by norm_num
    have h2 : t ^ 17 ≤ (1 / 2) ^ 17 := pow_le_pow_left₀ t0.le ht 17
    calc (4 * (1 + t)) ^ 3 * t ^ 17 ≤ 216 * (1 / 2) ^ 17 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num

/-- (8.11) [relationalbe] of Lemma 8.2 [FalFbe0] in the form `ρ^{±1/20}`, squared, for the
trial state. -/
theorem Lemma8_2_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ α β : Occ, ∀ v₁ v₂ v₃ : Idx,
      v₁ ≠ 0 → v₂ ≠ 0 → v₃ ≠ 0 → Legs_pm v₁ v₂ → Legs_pm v₁ v₃ → Legs_pm v₂ v₃ →
      InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β *
          (‖trialState V w kc N β‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁|) ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (‖trialState V w kc N α‖ ^ 2 *
            |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃| * ((α 0 : ℝ) / LN N ^ 3)) ∧
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (‖trialState V w kc N α‖ ^ 2 *
            |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃| * ((α 0 : ℝ) / LN N ^ 3)) ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β *
          (‖trialState V w kc N β‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁|) := by
  have hg := scat_g0_pos hV hw
  set δ : ℝ := min (1 / 2) ((2 * g0 V w) ^ 3) with hδ_def
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop 1).and ((Ratio_ev_lam hV hw).and (Ratio_ev_eps hδ)))
  refine ⟨N₀, fun N hN kc α β v₁ v₂ v₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ hne heq => ?_⟩
  obtain ⟨hN1, hl, hε⟩ := hN₀ N hN
  obtain ⟨hNL, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hc : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 := by unfold epsP; positivity
  have hR := Lemma8_2_ratio (V := V) (w := w) (kc := kc) hρ hL hNL hc
    (Ratio_hlam hV hw hN1 hl) h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ hne heq
  simp only at hR
  have hK := Ratio_K3 hρ hg (hε.trans (min_le_left _ _)) (hε.trans (min_le_right _ _))
  set K := max (4 * (mc (rhoN N) + 1)) (1 / (4 * (g0 V w / 2 * epsP (rhoN N) ^ 2)))
  set Y := ‖f0 V w (rhoN N) (LN N) β * csqrt (lam V w (rhoN N) (LN N) v₁)‖ ^ 2 with hY_def
  set X := ‖f0 V w (rhoN N) (LN N) α * csqrt (lam V w (rhoN N) (LN N) v₂) *
      csqrt (lam V w (rhoN N) (LN N) v₃)‖ ^ 2 * ((α 0 : ℝ) / LN N ^ 3) with hX_def
  have hY : ‖trialState V w kc N β‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁| = CN V w kc N ^ 2 * Y := by
    rw [hY_def, Ratio_trial_eq V w kc hβ, norm_mul, norm_mul, mul_pow, mul_pow,
      Ratio_norm_csqrt_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hX : ‖trialState V w kc N α‖ ^ 2 *
      |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃| * ((α 0 : ℝ) / LN N ^ 3) =
      CN V w kc N ^ 2 * X := by
    rw [hX_def, Ratio_trial_eq V w kc hα, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow,
      mul_pow, Ratio_norm_csqrt_sq, Ratio_norm_csqrt_sq, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, abs_mul]
    ring
  rw [hY, hX]
  have hX0 : 0 ≤ X := by rw [hX_def]; positivity
  have hY0 : 0 ≤ Y := by rw [hY_def]; positivity
  have hC := sq_nonneg (CN V w kc N)
  have hNα : (0 : ℝ) ≤ (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α := by positivity
  have hNβ : (0 : ℝ) ≤ (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β := by positivity
  constructor
  · calc (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * (CN V w kc N ^ 2 * Y)
        = CN V w kc N ^ 2 * ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * Y) := by ring
      _ ≤ CN V w kc N ^ 2 * (K ^ 3 * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * X) :=
          mul_le_mul_of_nonneg_left hR.1 hC
      _ ≤ CN V w kc N ^ 2 * (rhoN N ^ (-(1 / 10 : ℝ)) *
            (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * X) := by gcongr
      _ = _ := by ring
  · calc (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * (CN V w kc N ^ 2 * X)
        = CN V w kc N ^ 2 * ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * X) := by ring
      _ ≤ CN V w kc N ^ 2 * (K ^ 3 * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * Y) :=
          mul_le_mul_of_nonneg_left hR.2 hC
      _ ≤ CN V w kc N ^ 2 * (rhoN N ^ (-(1 / 10 : ℝ)) *
            (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * Y) := by gcongr
      _ = _ := by ring

/-- The coefficient of `a†_0 a†_{v₁} a_{v₂} a_{v₃}` in terms of `α = T(β)` and of `β`, for
nonzero, pairwise distinct `v₁, v₂, v₃`. -/
private lemma Ratio_c_sq_ab {v₁ v₂ v₃ : Idx} {α β : Occ} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃)
    (hne : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) (heq : (a4 0 v₁ v₂ v₃ β).2 = α) :
    (a4 0 v₁ v₂ v₃ β).1 ^ 2 =
        (α 0 : ℝ) * ((α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1)) ∧
      (a4 0 v₁ v₂ v₃ β).1 ^ 2 =
        (α 0 : ℝ) * (((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ)) ∧
      1 ≤ α v₁ ∧ 1 ≤ β v₂ ∧ 1 ≤ β v₃ := by
  obtain ⟨e0, e1, e2, e3⟩ := Ratio_a4_apply h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hne
  rw [heq] at e0 e1 e2 e3
  have hc := Ratio_c_sq β h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  refine ⟨?_, ?_, by omega, by omega, by omega⟩
  · rw [hc, ← e2, ← e3, e1, e0]
    push_cast
    ring
  · rw [hc, e0]
    push_cast
    ring

/-- On `M`, `α(n) ≤ N`. -/
private lemma Ratio_occ_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {α : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (n : Idx) : (α n : ℝ) ≤ N := by
  have h := (Ratio_occ_le_num α n).trans (MBasic_num (Particles_rhoN_LN hN).2.1 hα).le
  exact_mod_cast h

/-- (8.12) [fal0], squared and multiplied by `N^{F(β)} |λ_{v₁}|`. -/
theorem Eq8_12 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ α β : Occ, ∀ v₁ v₂ v₃ : Idx,
      v₁ ≠ 0 → v₂ ≠ 0 → v₃ ≠ 0 → Legs_pm v₁ v₂ → Legs_pm v₁ v₃ → Legs_pm v₂ v₃ →
      InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * |lam V w (rhoN N) (LN N) v₁| *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α + 1) *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          ((α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 4 := by
  obtain ⟨N₀, hN₀⟩ := Lemma8_2_paper hV hw
  refine ⟨max N₀ 1, fun N hN kc α β v₁ v₂ v₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ hne heq => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h := (hN₀ N (le_trans (le_max_left _ _) hN) kc α β v₁ v₂ v₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ
    hne heq).1
  obtain ⟨hNL, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hc := (Ratio_c_sq_ab h₁ h₂ h₃ h₁₂.1 h₁₃.1 h₂₃.1 hne heq).1
  have hα0 := Ratio_occ_le hN1 hα 0
  have hα0' : (α 0 : ℝ) * ((α 0 : ℝ) / LN N ^ 3) ≤ N * rhoN N := by
    have : (α 0 : ℝ) / LN N ^ 3 ≤ rhoN N := by
      rw [div_le_iff₀ (by positivity), hNL]
      exact hα0
    exact mul_le_mul hα0 this (by positivity) (by positivity)
  set A := ‖trialState V w kc N α‖
  set B := ‖trialState V w kc N β‖
  set c := (a4 0 v₁ v₂ v₃ β).1
  set R := rhoN N ^ (-(1 / 10 : ℝ))
  set P := (α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1)
  set l := |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|
  have hR : 0 ≤ R := by positivity
  have hP : 0 ≤ P := by positivity
  calc (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * |lam V w (rhoN N) (LN N) v₁| *
        (A * c * B) ^ 2
      = (c ^ 2 * A ^ 2) * ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β *
          (B ^ 2 * |lam V w (rhoN N) (LN N) v₁|)) := by ring
    _ ≤ (c ^ 2 * A ^ 2) * (R * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (A ^ 2 * l * ((α 0 : ℝ) / LN N ^ 3))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = R * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * l * P * A ^ 4 *
          ((α 0 : ℝ) * ((α 0 : ℝ) / LN N ^ 3)) := by rw [hc]; ring
    _ ≤ R * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * l * P * A ^ 4 *
          (N * rhoN N) := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- (8.13) [fbe0], squared and multiplied by `N^{F(α)} ρ |λ_{v₂} λ_{v₃}|`. -/
theorem Eq8_13 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ α β : Occ, ∀ v₁ v₂ v₃ : Idx,
      v₁ ≠ 0 → v₂ ≠ 0 → v₃ ≠ 0 → Legs_pm v₁ v₂ → Legs_pm v₁ v₃ → Legs_pm v₂ v₃ →
      InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β + 1) *
          |lam V w (rhoN N) (LN N) v₁| *
          (((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ)) * ‖trialState V w kc N β‖ ^ 4 := by
  obtain ⟨N₀, hN₀⟩ := Lemma8_2_paper hV hw
  refine ⟨max N₀ 1, fun N hN kc α β v₁ v₂ v₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ hne heq => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h := (hN₀ N (le_trans (le_max_left _ _) hN) kc α β v₁ v₂ v₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ
    hne heq).2
  obtain ⟨hNL, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hc := (Ratio_c_sq_ab h₁ h₂ h₃ h₁₂.1 h₁₃.1 h₂₃.1 hne heq).2.1
  have hρα : rhoN N * (α 0 : ℝ) = N * ((α 0 : ℝ) / LN N ^ 3) := by
    rw [← hNL]
    field_simp
  set A := ‖trialState V w kc N α‖
  set B := ‖trialState V w kc N β‖
  set c := (a4 0 v₁ v₂ v₃ β).1
  set R := rhoN N ^ (-(1 / 10 : ℝ))
  set P := ((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ)
  set l := |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|
  have hP : 0 ≤ P := by positivity
  calc (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * (rhoN N * l) * (A * c * B) ^ 2
      = (N * P * B ^ 2) * ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (A ^ 2 * l * ((α 0 : ℝ) / LN N ^ 3))) := by
        linear_combination ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * l * A ^ 2 * P *
          B ^ 2) * hρα + ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α * rhoN N * l * A ^ 2 *
          B ^ 2) * hc
    _ ≤ (N * P * B ^ 2) * (R * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β *
          (B ^ 2 * |lam V w (rhoN N) (LN N) v₁|)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- `N⁻¹ ≤ ρ_N`. -/
private lemma Ratio_inv_N_le {N : ℕ} (hN : 1 ≤ N) : (N : ℝ)⁻¹ ≤ rhoN N := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [rhoN, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/-- `ρ = ε^{200}`, (3.2) [defepseta]. -/
private lemma Ratio_rho_eps {ρ : ℝ} (hρ : 0 ≤ ρ) : ρ = epsP ρ ^ 200 := by
  rw [← Ratio_rpow_eps hρ 200 (x := 1) (by norm_num), Real.rpow_one]

/-- The branch `F(α) = 0` of (8.30)–(8.31), from (8.12) [fal0]. -/
private lemma Ratio_br31a {n ρ l₁ lℓ lh T A a₁ aℓ ah r M G p : ℝ} (hn : 0 < n)
    (hl₁ : 0 < l₁) (hlh : 0 ≤ lh) (haℓ : ρ * lℓ ≤ 1) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hM : 1 ≤ M) (hG : 0 ≤ G) (hp : 0 < p) (ha₁ : 1 ≤ a₁) (hah : 0 ≤ ah)
    (haℓ0 : 0 ≤ aℓ) (haℓM : aℓ + 1 ≤ M) (hl₁G : l₁ ≤ G / p ^ 2) (hlhG : lh ≤ 4 * G / p ^ 2)
    (h : n * l₁ * T ^ 2 ≤ r ^ 2 * n * (ρ * (lℓ * lh)) * (a₁ * ((aℓ + 1) * (ah + 1))) * A ^ 4) :
    T ≤ 2 * r * M * G / (p ^ 2 * l₁) * (a₁ * A ^ 2 + a₁ * ah * A ^ 2) := by
  set X := a₁ * A ^ 2 + a₁ * ah * A ^ 2 with hX_def
  have ha0 : 0 ≤ a₁ := by linarith
  have hX : 0 ≤ X := by rw [hX_def]; positivity
  have h' : l₁ * T ^ 2 ≤ r ^ 2 * (ρ * (lℓ * lh)) * (a₁ * ((aℓ + 1) * (ah + 1))) * A ^ 4 := by
    refine le_of_mul_le_mul_left ?_ hn
    calc n * (l₁ * T ^ 2) = n * l₁ * T ^ 2 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have hk : a₁ * (ah + 1) ≤ (a₁ * (1 + ah)) ^ 2 := by
    calc a₁ * (ah + 1) ≤ (a₁ * a₁) * ((ah + 1) * (ah + 1)) :=
          mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
      _ = _ := by ring
  have s1 : l₁ * T ^ 2 ≤ r ^ 2 * lh * M * X ^ 2 := by
    calc l₁ * T ^ 2 ≤ r ^ 2 * (ρ * (lℓ * lh)) * (a₁ * ((aℓ + 1) * (ah + 1))) * A ^ 4 := h'
      _ = r ^ 2 * lh * ((ρ * lℓ) * ((aℓ + 1) * (a₁ * (ah + 1)))) * A ^ 4 := by ring
      _ ≤ r ^ 2 * lh * (1 * (M * (a₁ * (1 + ah)) ^ 2)) * A ^ 4 := by
          gcongr
      _ = r ^ 2 * lh * M * X ^ 2 := by rw [hX_def]; ring
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have s2 : (l₁ * T) ^ 2 ≤ (2 * r * M * G * X / p ^ 2) ^ 2 := by
    calc (l₁ * T) ^ 2 = l₁ * (l₁ * T ^ 2) := by ring
      _ ≤ l₁ * (r ^ 2 * lh * M * X ^ 2) := by gcongr
      _ = r ^ 2 * M * X ^ 2 * (l₁ * lh) := by ring
      _ ≤ r ^ 2 * M ^ 2 * X ^ 2 * ((G / p ^ 2) * (4 * G / p ^ 2)) := by gcongr
      _ = (2 * r * M * G * X / p ^ 2) ^ 2 := by field_simp; ring
  have s3 : l₁ * T ≤ 2 * r * M * G * X / p ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 s2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at s3
  linarith

/-- The branch `F(β) = 0` of (8.30)–(8.31), from (8.13) [fbe0]. -/
private lemma Ratio_br31b {n ρ l₁ lℓ lh T B b₁ bℓ bh r M G p c₀ : ℝ} (hn : 0 < n)
    (hlh : 0 < lh) (hl₁ : 0 ≤ l₁) (hc₀ : 0 < c₀) (haℓ : c₀ ≤ ρ * lℓ) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hM : 1 ≤ M) (hG : 0 ≤ G) (hp : 0 < p) (hbh : 1 ≤ bh) (hb₁ : 0 ≤ b₁)
    (hbℓM : bℓ ≤ M) (hl₁G : l₁ ≤ G / p ^ 2) (hlhG : lh ≤ 4 * G / p ^ 2)
    (h : n * (ρ * (lℓ * lh)) * T ^ 2 ≤ r ^ 2 * n * l₁ * ((b₁ + 1) * (bℓ * bh)) * B ^ 4) :
    T ≤ 2 * r * M * (c₀⁻¹ + 1) * G / (p ^ 2 * lh) * (bh * B ^ 2 + b₁ * bh * B ^ 2) := by
  set Y := bh * B ^ 2 + b₁ * bh * B ^ 2 with hY_def
  have hb0 : 0 ≤ bh := by linarith
  have hY : 0 ≤ Y := by rw [hY_def]; positivity
  have h' : ρ * (lℓ * lh) * T ^ 2 ≤ r ^ 2 * l₁ * ((b₁ + 1) * (bℓ * bh)) * B ^ 4 := by
    refine le_of_mul_le_mul_left ?_ hn
    calc n * (ρ * (lℓ * lh) * T ^ 2) = n * (ρ * (lℓ * lh)) * T ^ 2 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have hk : (b₁ + 1) * bh ≤ (bh * (1 + b₁)) ^ 2 := by
    calc (b₁ + 1) * bh ≤ ((b₁ + 1) * (b₁ + 1)) * (bh * bh) :=
          mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
      _ = _ := by ring
  have s1 : c₀ * (lh * T ^ 2) ≤ r ^ 2 * l₁ * M * Y ^ 2 := by
    calc c₀ * (lh * T ^ 2) ≤ (ρ * lℓ) * (lh * T ^ 2) := by gcongr
      _ = ρ * (lℓ * lh) * T ^ 2 := by ring
      _ ≤ r ^ 2 * l₁ * ((b₁ + 1) * (bℓ * bh)) * B ^ 4 := h'
      _ = r ^ 2 * l₁ * (bℓ * ((b₁ + 1) * bh)) * B ^ 4 := by ring
      _ ≤ r ^ 2 * l₁ * (M * (bh * (1 + b₁)) ^ 2) * B ^ 4 := by
          gcongr
      _ = r ^ 2 * l₁ * M * Y ^ 2 := by rw [hY_def]; ring
  have hcM : 1 ≤ c₀ * M * (c₀⁻¹ + 1) ^ 2 := by
    have e : c₀ * (c₀⁻¹ + 1) ^ 2 = c₀⁻¹ + 2 + c₀ := by field_simp; ring
    have := inv_pos.2 hc₀
    have h1 : 1 ≤ c₀ * (c₀⁻¹ + 1) ^ 2 := by rw [e]; linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c₀ * (c₀⁻¹ + 1) ^ 2 * M := mul_le_mul h1 hM zero_le_one (by positivity)
      _ = c₀ * M * (c₀⁻¹ + 1) ^ 2 := by ring
  have s2 : c₀ * (lh * T) ^ 2 ≤ c₀ * (2 * r * M * (c₀⁻¹ + 1) * G * Y / p ^ 2) ^ 2 := by
    calc c₀ * (lh * T) ^ 2 = lh * (c₀ * (lh * T ^ 2)) := by ring
      _ ≤ lh * (r ^ 2 * l₁ * M * Y ^ 2) := by gcongr
      _ = r ^ 2 * M * Y ^ 2 * (l₁ * lh) := by ring
      _ ≤ r ^ 2 * M * Y ^ 2 * ((G / p ^ 2) * (4 * G / p ^ 2)) := by gcongr
      _ = (r ^ 2 * M * Y ^ 2 * (4 * G ^ 2 / p ^ 4)) * 1 := by field_simp
      _ ≤ (r ^ 2 * M * Y ^ 2 * (4 * G ^ 2 / p ^ 4)) * (c₀ * M * (c₀⁻¹ + 1) ^ 2) := by gcongr
      _ = c₀ * (2 * r * M * (c₀⁻¹ + 1) * G * Y / p ^ 2) ^ 2 := by field_simp; ring
  have s3 : lh * T ≤ 2 * r * M * (c₀⁻¹ + 1) * G * Y / p ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1
      (le_of_mul_le_mul_left s2 hc₀)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at s3
  linarith

/-- One summand of `Σ_β |Ψ(α)| ⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ |Ψ(β)|` in case (8.3)
[one0secondcase], with `{v₂, v₃} = {ℓ, h}`, `ℓ ∈ P_L`, `v₁, h ∈ P_H`: the bound of (8.30)–(8.31)
by `Q(v₁) + Q(v₁, h)` at `T(β)` and by `Q(h) + Q(v₁, h)` at `β`. -/
private lemma Ratio_term31 {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN1 : 1 ≤ N) {v₁ v₂ v₃ ℓ h : Idx}
    (hpair : (v₂ = ℓ ∧ v₃ = h) ∨ (v₂ = h ∧ v₃ = ℓ)) (hH₁ : inPH (rhoN N) (LN N) v₁)
    (hℓ : inPL (rhoN N) (LN N) ℓ) (hh : inPH (rhoN N) (LN N) h) (h0₁ : v₁ ≠ 0) (h0₂ : v₂ ≠ 0)
    (h0₃ : v₃ ≠ 0) (hp₁₂ : Legs_pm v₁ v₂) (hp₁₃ : Legs_pm v₁ v₃) (hp₂₃ : Legs_pm v₂ v₃)
    {c₀ r G : ℝ} (hc₀ : 0 < c₀) (hr0 : 0 ≤ r) (hr2 : rhoN N ^ (-(1 / 10 : ℝ)) = r ^ 2)
    (hG : 0 ≤ G)
    (ha : ∀ u, inPL (rhoN N) (LN N) u → c₀ ≤ rhoN N * |lam V w (rhoN N) (LN N) u| ∧
      rhoN N * |lam V w (rhoN N) (LN N) u| ≤ 1)
    (hp : 0 < ‖mom (LN N) v₁‖)
    (hl₁ : |lam V w (rhoN N) (LN N) v₁| ≤ G / ‖mom (LN N) v₁‖ ^ 2)
    (hlh : |lam V w (rhoN N) (LN N) h| ≤ 4 * G / ‖mom (LN N) v₁‖ ^ 2)
    (h12 : ∀ α β : Occ, InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * |lam V w (rhoN N) (LN N) v₁| *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α + 1) *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          ((α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 4)
    (h13 : ∀ α β : Occ, InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β + 1) *
          |lam V w (rhoN N) (LN N) v₁| *
          (((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ)) * ‖trialState V w kc N β‖ ^ 4)
    (β : Occ) :
    ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 *
        ‖trialState V w kc N β‖ ≤
      2 * r * (mc (rhoN N) + 2) * G /
          (‖mom (LN N) v₁‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁|) *
        (if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then
          ((a4 0 v₁ v₂ v₃ β).2 v₁ : ℝ) * ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 +
            ((a4 0 v₁ v₂ v₃ β).2 v₁ : ℝ) * ((a4 0 v₁ v₂ v₃ β).2 h : ℝ) *
              ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 else 0) +
      2 * r * (mc (rhoN N) + 2) * (c₀⁻¹ + 1) * G /
          (‖mom (LN N) v₁‖ ^ 2 * |lam V w (rhoN N) (LN N) h|) *
        ((β h : ℝ) * ‖trialState V w kc N β‖ ^ 2 +
          (β v₁ : ℝ) * (β h : ℝ) * ‖trialState V w kc N β‖ ^ 2) := by
  have hρ := (Particles_rhoN_LN hN1).2.1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN1
  have hmc0 : 0 ≤ mc (rhoN N) := by unfold mc rhoN; positivity
  have hM1 : 1 ≤ mc (rhoN N) + 2 := by linarith
  set SA := 2 * r * (mc (rhoN N) + 2) * G /
    (‖mom (LN N) v₁‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁|) with hSA
  set SB := 2 * r * (mc (rhoN N) + 2) * (c₀⁻¹ + 1) * G /
    (‖mom (LN N) v₁‖ ^ 2 * |lam V w (rhoN N) (LN N) h|) with hSB
  have hSA0 : 0 ≤ SA := by rw [hSA]; positivity
  have hSB0 : 0 ≤ SB := by rw [hSB]; positivity
  set hB := (β h : ℝ) * ‖trialState V w kc N β‖ ^ 2 +
    (β v₁ : ℝ) * (β h : ℝ) * ‖trialState V w kc N β‖ ^ 2 with hhB
  have hB0 : 0 ≤ hB := by rw [hhB]; positivity
  have hRHS : 0 ≤ SA * (if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then
      ((a4 0 v₁ v₂ v₃ β).2 v₁ : ℝ) * ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 +
        ((a4 0 v₁ v₂ v₃ β).2 v₁ : ℝ) * ((a4 0 v₁ v₂ v₃ β).2 h : ℝ) *
          ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 else 0) + SB * hB := by
    have : 0 ≤ (if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then
        ((a4 0 v₁ v₂ v₃ β).2 v₁ : ℝ) * ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 +
          ((a4 0 v₁ v₂ v₃ β).2 v₁ : ℝ) * ((a4 0 v₁ v₂ v₃ β).2 h : ℝ) *
            ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 else 0) := by
      split_ifs <;> positivity
    positivity
  by_cases hc : (a4 0 v₁ v₂ v₃ β).1 = 0
  · have e : ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 *
        ‖trialState V w kc N β‖ = 0 := by rw [hc, mul_zero, zero_mul]
    rw [e]
    exact hRHS
  by_cases hb : trialState V w kc N β = 0
  · have e : ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 *
        ‖trialState V w kc N β‖ = 0 := by rw [hb, norm_zero, mul_zero]
    rw [e]
    exact hRHS
  by_cases hav : trialState V w kc N (a4 0 v₁ v₂ v₃ β).2 = 0
  · have e : ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 *
        ‖trialState V w kc N β‖ = 0 := by rw [hav, norm_zero, zero_mul, zero_mul]
    rw [e]
    exact hRHS
  simp only [ne_eq, hc, not_false_eq_true, ite_true]
  generalize hα_def : (a4 0 v₁ v₂ v₃ β).2 = α at hav ⊢
  have hαM := Ratio_inM hav
  have hβM := Ratio_inM hb
  have hF := Lemma8_2_F hρ h0₁ h0₂ h0₃ hp₁₂ hp₁₃ hp₂₃ hαM hβM hc hα_def
  have hn₁ : ¬ inPL (rhoN N) (LN N) v₁ := fun h' => Regions_PL_PH hρ h' hH₁
  have hnh : ¬ inPL (rhoN N) (LN N) h := fun h' => Regions_PL_PH hρ h' hh
  have hcard : ({i | inPL (rhoN N) (LN N) (![v₁, v₂, v₃] i)} : Finset (Fin 3)).card = 1 := by
    rw [Finset.card_filter, Fin.sum_univ_three]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hn₁, hnh, hℓ]
  rw [hcard] at hF
  have hlam23 : |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃| =
      |lam V w (rhoN N) (LN N) ℓ| * |lam V w (rhoN N) (LN N) h| := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [abs_mul]; ring
  have hP23 : ∀ γ : Occ, ((γ v₂ : ℝ) + 1) * ((γ v₃ : ℝ) + 1) =
      ((γ ℓ : ℝ) + 1) * ((γ h : ℝ) + 1) := fun γ => by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
  have hQ23 : ∀ γ : Occ, (γ v₂ : ℝ) * (γ v₃ : ℝ) = (γ ℓ : ℝ) * (γ h : ℝ) := fun γ => by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
  obtain ⟨-, -, hα₁, hβ₂, hβ₃⟩ := Ratio_c_sq_ab h0₁ h0₂ h0₃ hp₁₂.1 hp₁₃.1 hp₂₃.1 hc hα_def
  have hβh : 1 ≤ β h := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hT0 : 0 ≤ ‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖ := by
    have := a4_fst_nonneg 0 v₁ v₂ v₃ β
    positivity
  obtain ⟨haℓ, haℓ'⟩ := ha ℓ hℓ
  have hstar : ∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → (γ ℓ : ℝ) ≤ mc (rhoN N) + 1 :=
    fun γ hγ => ((Nat.cast_le.2 (le_max_left _ _)).trans_lt (MStar_PL_mc hρ hγ hℓ)).le
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (show Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α ≤ 1 by
    omega) with hFα | hFα
  · have hFβ : Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β = 1 := by omega
    have hl₁0 : 0 < |lam V w (rhoN N) (LN N) v₁| := by
      refine abs_pos.2 fun h0 => hav ?_
      exact Ratio_trial_zero V w kc N h0₁ h0 hα₁
    have h' := h12 α β hαM hβM hc hα_def
    rw [hr2, hFα, hFβ, hlam23] at h'
    have hfin := Ratio_br31a (n := (N : ℝ)) (ρ := rhoN N) (lℓ := |lam V w (rhoN N) (LN N) ℓ|)
      (A := ‖trialState V w kc N α‖) (aℓ := (α ℓ : ℝ)) (a₁ := (α v₁ : ℝ))
      (ah := (α h : ℝ)) hn hl₁0 (abs_nonneg _) haℓ' hT0 hr0
      hM1 hG hp (by exact_mod_cast hα₁) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by linarith [hstar α hαM]) hl₁ hlh (by
        calc (N : ℝ) * |lam V w (rhoN N) (LN N) v₁| *
              (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2
            = (N : ℝ) ^ 1 * |lam V w (rhoN N) (LN N) v₁| *
              (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 := by
              rw [pow_one]
          _ ≤ _ := h'
          _ = _ := by
              rw [zero_add, pow_one, mul_assoc (α v₁ : ℝ), hP23 α])
    calc _ ≤ _ := hfin
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hSB0 hB0)
  · have hFβ : Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β = 0 := by omega
    have hlh0 : 0 < |lam V w (rhoN N) (LN N) h| := by
      refine abs_pos.2 fun h0 => hb ?_
      exact Ratio_trial_zero V w kc N (Regions_PH_ne_zero hρ hh) h0 hβh
    have h' := h13 α β hαM hβM hc hα_def
    rw [hr2, hFα, hFβ, hlam23] at h'
    have hfin := Ratio_br31b (n := (N : ℝ)) (ρ := rhoN N) (lℓ := |lam V w (rhoN N) (LN N) ℓ|)
      (B := ‖trialState V w kc N β‖) (bℓ := (β ℓ : ℝ)) (bh := (β h : ℝ))
      (b₁ := (β v₁ : ℝ)) hn hlh0 (abs_nonneg _) hc₀ haℓ hT0 hr0
      hM1 hG hp (by exact_mod_cast hβh) (Nat.cast_nonneg _)
      (by linarith [hstar β hβM]) hl₁ hlh (by
        calc (N : ℝ) * (rhoN N * (|lam V w (rhoN N) (LN N) ℓ| * |lam V w (rhoN N) (LN N) h|)) *
              (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2
            = (N : ℝ) ^ 1 * (rhoN N * (|lam V w (rhoN N) (LN N) ℓ| *
                |lam V w (rhoN N) (LN N) h|)) *
              (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 := by
              rw [pow_one]
          _ ≤ _ := h'
          _ = _ := by
              rw [zero_add, pow_one, mul_assoc ((β v₁ : ℝ) + 1), hQ23 β])
    have hA0 : 0 ≤ (α v₁ : ℝ) * ‖trialState V w kc N α‖ ^ 2 +
        (α v₁ : ℝ) * (α h : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by positivity
    calc _ ≤ _ := hfin
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hSA0 hA0)

/-- `(A / (q l)) x ≤ (A / q) K` when `x ≤ l K`; the case `l = 0` is trivial. -/
private lemma Ratio_div_mul_le {A q l x K : ℝ} (hA : 0 ≤ A) (hq : 0 < q) (hl : 0 ≤ l)
    (hK : 0 ≤ K) (hx : x ≤ l * K) : A / (q * l) * x ≤ A / q * K := by
  rcases hl.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, div_zero, zero_mul]
    positivity
  · calc A / (q * l) * x ≤ A / (q * l) * (l * K) := by gcongr
      _ = A / q * K := by field_simp

/-- The final count of (8.31) for the two branches. -/
private lemma Ratio_fin31 {r M K G C₁ C₂ X Y p : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hK : 1 ≤ K)
    (hG : 0 ≤ G) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hX : 0 ≤ X) (hY : Y ≤ X)
    (hp : 0 < p) :
    2 * r * M * G / p ^ 2 * (C₁ * X / p ^ 2 + C₂ * (4 * G / p ^ 2) * Y) +
        2 * r * M * K * G / p ^ 2 * (C₁ * X * (4 / p ^ 2) + C₂ * (G / p ^ 2) * Y) ≤
      10 * G * (C₁ + C₂ * G) * (r * M * K * X) / p ^ 4 := by
  have e : 2 * r * M * G / p ^ 2 * (C₁ * X / p ^ 2 + C₂ * (4 * G / p ^ 2) * Y) +
      2 * r * M * K * G / p ^ 2 * (C₁ * X * (4 / p ^ 2) + C₂ * (G / p ^ 2) * Y) =
      2 * r * M * G * (C₁ * X + 4 * (C₂ * G * Y) + K * (4 * (C₁ * X) + C₂ * G * Y)) / p ^ 4 := by
    field_simp
  rw [e]
  have h1 : C₁ * X ≤ K * (C₁ * X) := le_mul_of_one_le_left (by positivity) hK
  have h2 : C₂ * G * Y ≤ C₂ * G * X := by gcongr
  have h3 : C₂ * G * X ≤ K * (C₂ * G * X) := le_mul_of_one_le_left (by positivity) hK
  have h4 : K * (C₂ * G * Y) ≤ K * (C₂ * G * X) := by gcongr
  have hb : C₁ * X + 4 * (C₂ * G * Y) + K * (4 * (C₁ * X) + C₂ * G * Y) ≤
      5 * K * (C₁ + C₂ * G) * X := by nlinarith
  calc 2 * r * M * G * (C₁ * X + 4 * (C₂ * G * Y) + K * (4 * (C₁ * X) + C₂ * G * Y)) / p ^ 4
      ≤ 2 * r * M * G * (5 * K * (C₁ + C₂ * G) * X) / p ^ 4 := by gcongr
    _ = _ := by ring

/-- `r M (c₀⁻¹ + 1) ρ² ≤ 3 (2/g + 1) ρ^{2 - 1/10}` in powers of `t = ε`. -/
private lemma Ratio_fin31t {t g : ℝ} (t0 : 0 < t) (t1 : t ≤ 1) (hg : 0 < g) :
    (t ^ 10)⁻¹ * (t⁻¹ + 2) * ((g / 2 * t ^ 2)⁻¹ + 1) * (t ^ 200) ^ 2 ≤
      3 * (2 / g + 1) * t ^ 380 := by
  have ha : ((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2 ≤ 2 / g + 1 := by
    have e : ((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2 = 2 / g + t ^ 2 := by field_simp
    rw [e]
    nlinarith [pow_le_one₀ t0.le t1 (n := 2)]
  have hb : (t⁻¹ + 2) * t ≤ 3 := by
    have e : (t⁻¹ + 2) * t = 1 + 2 * t := by field_simp
    rw [e]
    linarith
  have e2 : t ^ 400 * (t ^ 13)⁻¹ = t ^ 387 := by rw [← pow_sub₀ _ t0.ne' (by norm_num)]
  have e : (t ^ 10)⁻¹ * (t⁻¹ + 2) * ((g / 2 * t ^ 2)⁻¹ + 1) * (t ^ 200) ^ 2 =
      ((t⁻¹ + 2) * t) * (((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2) * (t ^ 400 * (t ^ 13)⁻¹) := by
    field_simp
  rw [e, e2]
  have h0a : 0 ≤ ((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2 := by positivity
  have h0b : 0 ≤ (t⁻¹ + 2) * t := by positivity
  calc _ ≤ 3 * (2 / g + 1) * t ^ 387 := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t0.le t1 (by norm_num))
        (by positivity)

private lemma Ratio_pm_symm {a b : Idx} (h : Legs_pm a b) : Legs_pm b a :=
  ⟨fun e => h.1 e.symm, fun e => h.2 (by rw [e, neg_neg])⟩

/-- (8.30)–(8.31) for one pair in case (8.3) [one0secondcase], with `{v₂, v₃} = {ℓ, h}`,
`ℓ ∈ P_L`, `v₁, h ∈ P_H`, `h = v₁ - ℓ`, at a fixed large `N`. -/
private lemma Ratio_core31 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    {kc : ℝ} {N : ℕ} (hN1 : 1 ≤ N)
    (hl : ∀ (L : ℝ) (n : Idx), inPL (rhoN N) L n →
      lam V w (rhoN N) L n ≤ -(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹)
    (hε : epsP (rhoN N) ≤ 1 / 2) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hQ1 : ∀ u : Idx, inPH (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        C₁ * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2)
    (hQ2 : ∀ u v : Idx, inPH (rhoN N) (LN N) u → inPH (rhoN N) (LN N) v → u ≠ v → u + v ≠ 0 →
      Expect.Q (trialState V w kc N) [u, v] ≤
        C₂ * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 4 /
          epsP (rhoN N) ^ 4)
    (h12 : ∀ (α β : Occ) (v₁ v₂ v₃ : Idx),
      v₁ ≠ 0 → v₂ ≠ 0 → v₃ ≠ 0 → Legs_pm v₁ v₂ → Legs_pm v₁ v₃ → Legs_pm v₂ v₃ →
      InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * |lam V w (rhoN N) (LN N) v₁| *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α + 1) *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          ((α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 4)
    (h13 : ∀ (α β : Occ) (v₁ v₂ v₃ : Idx),
      v₁ ≠ 0 → v₂ ≠ 0 → v₃ ≠ 0 → Legs_pm v₁ v₂ → Legs_pm v₁ v₃ → Legs_pm v₂ v₃ →
      InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β + 1) *
          |lam V w (rhoN N) (LN N) v₁| *
          (((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ)) * ‖trialState V w kc N β‖ ^ 4)
    {v₁ v₂ v₃ ℓ h : Idx} (hpair : (v₂ = ℓ ∧ v₃ = h) ∨ (v₂ = h ∧ v₃ = ℓ))
    (hH₁ : inPH (rhoN N) (LN N) v₁) (hℓ : inPL (rhoN N) (LN N) ℓ)
    (hh : inPH (rhoN N) (LN N) h) (hhℓ : h = v₁ - ℓ) :
    OneLeg_absA (trialState V w kc N) v₁ v₂ v₃ ≤
      30 * (∫ x, |gfun V w x|) * (C₁ + C₂ * ∫ x, |gfun V w x|) * (2 / g0 V w + 1) *
        rhoN N ^ (2 - 1/10 : ℝ) / ‖mom (LN N) v₁‖ ^ 4 := by
  have hg := scat_g0_pos hV hw
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set G := ∫ x, |gfun V w x| with hG_def
  have hG : 0 ≤ G := integral_nonneg fun x => abs_nonneg _
  set t := epsP (rhoN N) with ht_def
  have t0 : 0 < t := by rw [ht_def, epsP]; positivity
  have t1 : t ≤ 1 := hε.trans (by norm_num)
  -- distinctness of the legs
  have h0₁ := Regions_PH_ne_zero hρ hH₁
  have h0ℓ := Regions_PL_ne_zero hρ hℓ
  have h0h := Regions_PH_ne_zero hρ hh
  have hnL₁ : ¬ inPL (rhoN N) (LN N) v₁ := fun h' => Regions_PL_PH hρ h' hH₁
  have hnLh : ¬ inPL (rhoN N) (LN N) h := fun h' => Regions_PL_PH hρ h' hh
  have hpm₁ℓ : Legs_pm v₁ ℓ :=
    ⟨fun e => hnL₁ (e ▸ hℓ), fun e => hnL₁ (by rw [e]; exact Regions_PL_neg.2 hℓ)⟩
  have hpmℓh : Legs_pm ℓ h :=
    ⟨fun e => hnLh (e ▸ hℓ), fun e => hnLh (by
      rw [show h = -ℓ by rw [e, neg_neg]]; exact Regions_PL_neg.2 hℓ)⟩
  have hdbl : ℓ ≠ v₁ + v₁ := fun e => Regions_PH_two hρ hH₁ (e ▸ hℓ)
  have hpm₁h : Legs_pm v₁ h :=
    ⟨fun e => h0ℓ (by rw [hhℓ] at e; linear_combination e),
      fun e => hdbl (by rw [hhℓ] at e; linear_combination -e)⟩
  have hsum₁h : v₁ + h ≠ 0 := fun e => hdbl (by rw [hhℓ] at e; linear_combination -e)
  have h0₂ : v₂ ≠ 0 := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h0₃ : v₃ ≠ 0 := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hp₁₂ : Legs_pm v₁ v₂ := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hp₁₃ : Legs_pm v₁ v₃ := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hp₂₃ : Legs_pm v₂ v₃ := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpmℓh
    · exact Ratio_pm_symm hpmℓh
  -- momenta
  set p := ‖mom (LN N) v₁‖ with hp_def
  have hpt : t < p := hH₁
  have hp : 0 < p := t0.trans hpt
  have hℓt : ‖mom (LN N) ℓ‖ ≤ t / 2 := by
    have h1 := hℓ.2
    rw [Ratio_rpow_eps hρ.le 100 (by norm_num)] at h1
    have h2 : t ^ 98 ≤ 1 / 2 := (pow_le_pow_of_le_one t0.le t1 (by norm_num : 1 ≤ 98)).trans
      (by rw [pow_one]; exact hε)
    calc ‖mom (LN N) ℓ‖ ≤ t⁻¹ * t ^ 100 := h1
      _ = t * t ^ 98 := by field_simp
      _ ≤ t * (1 / 2) := by gcongr
      _ = t / 2 := by ring
  have hph : p / 2 ≤ ‖mom (LN N) h‖ := by
    have e : mom (LN N) h = mom (LN N) v₁ - mom (LN N) ℓ := by
      rw [hhℓ]; ext i; simp [mom]; ring
    have := norm_sub_norm_le (mom (LN N) v₁) (mom (LN N) ℓ)
    rw [← e] at this
    linarith
  have hph0 : 0 < ‖mom (LN N) h‖ := by linarith
  have hph4 : 1 / ‖mom (LN N) h‖ ^ 2 ≤ 4 / p ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hl₁ : |lam V w (rhoN N) (LN N) v₁| ≤ G / p ^ 2 := Particles_lam_abs_le V w _ _ v₁ hnL₁
  have hlh' : |lam V w (rhoN N) (LN N) h| ≤ G / ‖mom (LN N) h‖ ^ 2 :=
    Particles_lam_abs_le V w _ _ h hnLh
  have hlh : |lam V w (rhoN N) (LN N) h| ≤ 4 * G / p ^ 2 := by
    calc _ ≤ G / ‖mom (LN N) h‖ ^ 2 := hlh'
      _ = G * (1 / ‖mom (LN N) h‖ ^ 2) := by ring
      _ ≤ G * (4 / p ^ 2) := by gcongr
      _ = 4 * G / p ^ 2 := by ring
  -- constants
  have hΨ := Normalization_isNState V w kc hN1
  set c₀ := g0 V w / 2 * t ^ 2 with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  set r := (t ^ 10)⁻¹ with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr2 : rhoN N ^ (-(1 / 10 : ℝ)) = r ^ 2 := by
    rw [Ratio_rpow_eps_neg hρ.le 20 (by norm_num), hr_def, inv_pow, ← pow_mul]
  have hmc : mc (rhoN N) = t⁻¹ := Ratio_mc hρ.le
  have ha : ∀ u, inPL (rhoN N) (LN N) u →
      c₀ ≤ rhoN N * |lam V w (rhoN N) (LN N) u| ∧ rhoN N * |lam V w (rhoN N) (LN N) u| ≤ 1 := by
    intro u hu
    have h1 := Ratio_hlam hV hw hN1 hl u hu
    have h2 := (scat_lam_PL hV hw _ hρ _ u hu).2
    rw [abs_of_neg h2, mul_neg]
    exact h1
  -- one summand
  have hterm := Ratio_term31 (V := V) (w := w) (kc := kc) hN1 hpair hH₁ hℓ hh h0₁ h0₂ h0₃
    hp₁₂ hp₁₃ hp₂₃ hc₀ hr0 hr2 hG ha hp hl₁ hlh
    (fun α β => h12 α β v₁ v₂ v₃ h0₁ h0₂ h0₃ hp₁₂ hp₁₃ hp₂₃)
    (fun α β => h13 α β v₁ v₂ v₃ h0₁ h0₂ h0₃ hp₁₂ hp₁₃ hp₂₃)
  set Ψ := trialState V w kc N with hΨ_def
  set l₁ := |lam V w (rhoN N) (LN N) v₁| with hl₁_def
  set lh := |lam V w (rhoN N) (LN N) h| with hlh_def
  set M := mc (rhoN N) + 2 with hM_def
  have hM0 : 0 ≤ M := by rw [hM_def, hmc]; positivity
  set SA := 2 * r * M * G / (p ^ 2 * l₁) with hSA
  set SB := 2 * r * M * (c₀⁻¹ + 1) * G / (p ^ 2 * lh) with hSB
  have hSA0 : 0 ≤ SA := by rw [hSA]; positivity
  have hSB0 : 0 ≤ SB := by rw [hSB]; positivity
  -- the series
  have hNnum : ∀ γ : Occ, γ.num = N → ∀ u, (γ u : ℝ) ≤ N := fun γ hγ u => by
    have := (Ratio_occ_le_num γ u).trans hγ.le
    exact_mod_cast this
  have hs1 : ∀ u, Summable fun γ : Occ => (γ u : ℝ) * ‖Ψ γ‖ ^ 2 := fun u =>
    Ratio_summable_w hΨ (fun γ => (γ u : ℝ)) N fun γ hγ => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact hNnum γ hγ u
  have hs2 : ∀ u v, Summable fun γ : Occ => (γ u : ℝ) * (γ v : ℝ) * ‖Ψ γ‖ ^ 2 := fun u v =>
    Ratio_summable_w hΨ (fun γ => (γ u : ℝ) * (γ v : ℝ)) ((N : ℝ) * N) fun γ hγ => by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (hNnum γ hγ u) (hNnum γ hγ v) (by positivity) (by positivity)
  set hA : Occ → ℝ := fun γ => (γ v₁ : ℝ) * ‖Ψ γ‖ ^ 2 + (γ v₁ : ℝ) * (γ h : ℝ) * ‖Ψ γ‖ ^ 2
    with hhA
  set hB : Occ → ℝ := fun γ => (γ h : ℝ) * ‖Ψ γ‖ ^ 2 + (γ v₁ : ℝ) * (γ h : ℝ) * ‖Ψ γ‖ ^ 2
    with hhB
  have hA0 : ∀ γ, 0 ≤ hA γ := fun γ => by simp only [hhA]; positivity
  have hB0 : ∀ γ, 0 ≤ hB γ := fun γ => by simp only [hhB]; positivity
  have hAs : Summable hA := (hs1 v₁).add (hs2 v₁ h)
  have hBs : Summable hB := (hs1 h).add (hs2 v₁ h)
  have hAsum : ∑' γ, hA γ = Expect.Q Ψ [v₁] + Expect.Q Ψ [v₁, h] := by
    rw [Ratio_Q1, Ratio_Q2, ← (hs1 v₁).tsum_add (hs2 v₁ h)]
  have hBsum : ∑' γ, hB γ = Expect.Q Ψ [h] + Expect.Q Ψ [v₁, h] := by
    rw [Ratio_Q1, Ratio_Q2, ← (hs1 h).tsum_add (hs2 v₁ h)]
  obtain ⟨hgAs, hgA⟩ := Ratio_reindex 0 v₁ v₂ v₃ hA0 hAs
  set gA : Occ → ℝ := fun β =>
    if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then hA (a4 0 v₁ v₂ v₃ β).2 else 0 with hgA_def
  have hterm' : ∀ β, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖ ≤
      SA * gA β + SB * hB β := fun β => hterm β
  have hsum : Summable fun β => SA * gA β + SB * hB β :=
    (hgAs.mul_left SA).add (hBs.mul_left SB)
  have hnn : ∀ β, 0 ≤ ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖ := fun β => by
    have := a4_fst_nonneg 0 v₁ v₂ v₃ β
    positivity
  -- the bounds of Lemma 5.4 [lem1] and (5.42)
  set Y := rhoN N ^ 4 / t ^ 4 with hY_def
  set X := rhoN N ^ 2 with hX_def
  have hρt : rhoN N = t ^ 200 := Ratio_rho_eps hρ.le
  have hYX : Y ≤ X := by
    rw [hY_def, hX_def, hρt, ← pow_mul, ← pow_mul, div_le_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_of_le_one t0.le t1 (by norm_num)
  have hQ₁ := hQ1 v₁ hH₁
  have hQh := hQ1 h hh
  have hQ₁h := hQ2 v₁ h hH₁ hh hpm₁h.1 hsum₁h
  rw [abs_mul] at hQ₁h
  have hxA : Expect.Q Ψ [v₁] + Expect.Q Ψ [v₁, h] ≤
      l₁ * (C₁ * X / p ^ 2 + C₂ * (4 * G / p ^ 2) * Y) := by
    have e1 : C₁ * rhoN N ^ 2 * l₁ / p ^ 2 = l₁ * (C₁ * X / p ^ 2) := by ring
    have e2 : C₂ * (l₁ * lh) * rhoN N ^ 4 / t ^ 4 = l₁ * (C₂ * lh * Y) := by ring
    have : l₁ * (C₂ * lh * Y) ≤ l₁ * (C₂ * (4 * G / p ^ 2) * Y) := by
      have : 0 ≤ Y := by positivity
      gcongr
    have hQ₁' : Expect.Q Ψ [v₁] ≤ l₁ * (C₁ * X / p ^ 2) := e1 ▸ hQ₁
    have hQ₁h' : Expect.Q Ψ [v₁, h] ≤ l₁ * (C₂ * lh * Y) := e2 ▸ hQ₁h
    linarith
  have hxB : Expect.Q Ψ [h] + Expect.Q Ψ [v₁, h] ≤
      lh * (C₁ * X * (4 / p ^ 2) + C₂ * (G / p ^ 2) * Y) := by
    have e1 : C₁ * rhoN N ^ 2 * lh / ‖mom (LN N) h‖ ^ 2 =
        lh * (C₁ * X * (1 / ‖mom (LN N) h‖ ^ 2)) := by ring
    have e2 : C₂ * (l₁ * lh) * rhoN N ^ 4 / t ^ 4 = lh * (C₂ * l₁ * Y) := by ring
    have h1 : lh * (C₁ * X * (1 / ‖mom (LN N) h‖ ^ 2)) ≤ lh * (C₁ * X * (4 / p ^ 2)) := by
      gcongr
    have h2 : lh * (C₂ * l₁ * Y) ≤ lh * (C₂ * (G / p ^ 2) * Y) := by
      have : 0 ≤ Y := by positivity
      gcongr
    have hQh' : Expect.Q Ψ [h] ≤ lh * (C₁ * X * (1 / ‖mom (LN N) h‖ ^ 2)) := e1 ▸ hQh
    have hQ₁h' : Expect.Q Ψ [v₁, h] ≤ lh * (C₂ * l₁ * Y) := e2 ▸ hQ₁h
    linarith
  unfold OneLeg_absA
  calc (∑' β, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖)
      ≤ ∑' β, (SA * gA β + SB * hB β) :=
        (Summable.of_nonneg_of_le hnn hterm' hsum).tsum_le_tsum hterm' hsum
    _ = SA * (∑' β, gA β) + SB * (∑' β, hB β) := by
        rw [(hgAs.mul_left SA).tsum_add (hBs.mul_left SB), tsum_mul_left, tsum_mul_left]
    _ ≤ SA * (∑' γ, hA γ) + SB * (∑' β, hB β) := by gcongr
    _ = SA * (Expect.Q Ψ [v₁] + Expect.Q Ψ [v₁, h]) +
          SB * (Expect.Q Ψ [h] + Expect.Q Ψ [v₁, h]) := by rw [hAsum, hBsum]
    _ ≤ 2 * r * M * G / p ^ 2 * (C₁ * X / p ^ 2 + C₂ * (4 * G / p ^ 2) * Y) +
          2 * r * M * (c₀⁻¹ + 1) * G / p ^ 2 *
            (C₁ * X * (4 / p ^ 2) + C₂ * (G / p ^ 2) * Y) := by
        have hY0 : 0 ≤ Y := by positivity
        exact add_le_add
          (Ratio_div_mul_le (by positivity) (by positivity) (abs_nonneg _) (by positivity) hxA)
          (Ratio_div_mul_le (by positivity) (by positivity) (abs_nonneg _) (by positivity) hxB)
    _ ≤ 10 * G * (C₁ + C₂ * G) * (r * M * (c₀⁻¹ + 1) * X) / p ^ 4 :=
        Ratio_fin31 hr0 hM0 (by have := inv_pos.2 hc₀; linarith) hG hC₁ hC₂ (by positivity)
          hYX hp
    _ ≤ 10 * G * (C₁ + C₂ * G) * (3 * (2 / g0 V w + 1) * t ^ 380) / p ^ 4 := by
        gcongr 10 * G * (C₁ + C₂ * G) * ?_ / p ^ 4
        rw [hr_def, hM_def, hmc, hc₀_def, hX_def, hρt]
        exact Ratio_fin31t t0 t1 hg
    _ = _ := by
        rw [Ratio_rpow_eps hρ.le 380 (by norm_num)]
        ring

/-- (8.30)–(8.31) for one pair in case (8.3) [one0secondcase], with the decay in `|v₁|` that
makes the sum over `v₁ ∈ P_H` uniform in `k_c`. -/
theorem Eq8_31 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ v₁ v₂ : Idx,
      OneLeg_case2 (rhoN N) (LN N) kc v₁ v₂ →
      OneLeg_absA (trialState V w kc N) v₁ v₂ (v₁ - v₂) ≤
        C * rhoN N ^ (2 - 1/10 : ℝ) / ‖mom (LN N) v₁‖ ^ 4 := by
  obtain ⟨N₁, h12⟩ := Eq8_12 hV hw
  obtain ⟨N₂, h13⟩ := Eq8_13 hV hw
  obtain ⟨C₁, hC₁, N₃, hQ1⟩ := Lemma5_4_PH V w
  obtain ⟨C₂, hC₂, N₄, hQ2⟩ := Eq5_42 V w
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop (max (max N₁ N₂) (max (max N₃ N₄) 1))).and
      ((Ratio_ev_lam hV hw).and (Ratio_ev_eps (δ := 1 / 2) (by norm_num))))
  have hg := scat_g0_pos hV hw
  have hG : 0 ≤ ∫ x, |gfun V w x| := integral_nonneg fun x => abs_nonneg _
  refine ⟨30 * (∫ x, |gfun V w x|) * (C₁ + C₂ * ∫ x, |gfun V w x|) * (2 / g0 V w + 1),
    by positivity, N₀, fun N hN kc v₁ v₂ hcase => ?_⟩
  obtain ⟨hNmax, hl, hε⟩ := hN₀ N hN
  have hNN₁ : N ≥ N₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNmax
  have hNN₂ : N ≥ N₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNmax
  have hNN₃ : N ≥ N₃ := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hNmax
  have hNN₄ : N ≥ N₄ := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hNmax
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNmax
  have core := @Ratio_core31 V w hV hw kc N hN1 hl hε C₁ C₂ hC₁ hC₂
    (fun u hu => hQ1 N hNN₃ kc u hu)
    (fun u v hu hv huv hs => hQ2 N hNN₄ kc u v hu hv huv hs)
    (fun α β v₁ v₂ v₃ => h12 N hNN₁ kc α β v₁ v₂ v₃)
    (fun α β v₁ v₂ v₃ => h13 N hNN₂ kc α β v₁ v₂ v₃)
  rcases hcase with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact core (ℓ := v₂) (h := v₁ - v₂) (Or.inl ⟨rfl, rfl⟩) h₁.1 h₂ h₃.1 rfl
  · exact core (ℓ := v₁ - v₂) (h := v₂) (Or.inr ⟨rfl, rfl⟩) h₁.1 h₃ h₂.1
      (sub_sub_cancel v₁ v₂).symm

/-- For `v₁, v₂, v₃ ∈ P_L` and `β, T(β) ∈ M`:
`⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ ≤ √N (m_c + 1)^{3/2}`. -/
private lemma Ratio_c_le_PL {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {v₁ v₂ v₃ : Idx} {β : Occ}
    (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (hβ : InM (rhoN N) (LN N) kc N β)
    (hα : InM (rhoN N) (LN N) kc N (a4 0 v₁ v₂ v₃ β).2) :
    (a4 0 v₁ v₂ v₃ β).1 ≤ Real.sqrt N * (mc (rhoN N) + 1) ^ (3 / 2 : ℝ) := by
  have hρ := (Particles_rhoN_LN hN).2.1
  have hm : 0 ≤ mc (rhoN N) + 1 := by unfold mc rhoN; positivity
  have hstar : ∀ {γ : Occ} {u : Idx}, InM (rhoN N) (LN N) kc N γ → inPL (rhoN N) (LN N) u →
      (γ u : ℝ) ≤ mc (rhoN N) + 1 := fun hγ hu =>
    ((Nat.cast_le.2 (le_max_left _ _)).trans_lt (MStar_PL_mc hρ hγ hu)).le
  have hα0 := Ratio_occ_le hN hα 0
  have hα1 := hstar hα h₁
  have e : (mc (rhoN N) + 1) ^ (3 / 2 : ℝ) =
      Real.sqrt (mc (rhoN N) + 1) * Real.sqrt (mc (rhoN N) + 1) *
        Real.sqrt (mc (rhoN N) + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hm (by norm_num),
      ← Real.rpow_add' hm (by norm_num)]
    norm_num
  rw [e]
  simp only [a4] at hα0 hα1 ⊢
  have hb2 : (((β - Finsupp.single v₃ 1 : Occ) v₂ : ℕ) : ℝ) ≤ mc (rhoN N) + 1 :=
    (Nat.cast_le.2 (tsub_le_self (a := β v₂))).trans (hstar hβ h₂)
  have hb1 : (((β - Finsupp.single v₃ 1 - Finsupp.single v₂ 1 + Finsupp.single v₁ 1 : Occ) v₁ :
      ℕ) : ℝ) ≤
      mc (rhoN N) + 1 := by
    refine le_trans ?_ hα1
    exact_mod_cast le_self_add
  calc _ ≤ Real.sqrt (mc (rhoN N) + 1) * Real.sqrt (mc (rhoN N) + 1) *
        Real.sqrt (mc (rhoN N) + 1) * Real.sqrt N := by
        gcongr
        exact hstar hβ h₃
    _ = _ := by ring

/-- The bound behind (8.32): for `v₁, v₂, v₃ ∈ P_L`,
`Σ_β |Ψ(α)| ⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ |Ψ(β)| ≤ √N (m_c + 1)^{3/2}`. -/
theorem Eq8_32 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {v₁ v₂ v₃ : Idx}
    (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) :
    OneLeg_absA (trialState V w kc N) v₁ v₂ v₃ ≤
      Real.sqrt N * (mc (rhoN N) + 1) ^ (3/2 : ℝ) := by
  have hΨ := Normalization_isNState V w kc hN
  set Ψ := trialState V w kc N with hΨ_def
  set B := Real.sqrt N * (mc (rhoN N) + 1) ^ (3 / 2 : ℝ)
  have hm : 0 ≤ mc (rhoN N) + 1 := by unfold mc rhoN; positivity
  have hB0 : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hm _)
  have hs : Summable fun γ => ‖Ψ γ‖ ^ 2 := hΨ.1.summable
  obtain ⟨hgs, hg⟩ := Ratio_reindex 0 v₁ v₂ v₃ (h := fun γ => ‖Ψ γ‖ ^ 2) (fun _ => by positivity) hs
  set g := fun β => if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 else 0
  have hterm : ∀ β, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖ ≤
      B / 2 * (g β + ‖Ψ β‖ ^ 2) := by
    intro β
    have hg0 : 0 ≤ g β := by simp only [g]; split_ifs <;> positivity
    by_cases hc : (a4 0 v₁ v₂ v₃ β).1 = 0
    · rw [hc, mul_zero, zero_mul]
      positivity
    by_cases hb : Ψ β = 0
    · rw [hb, norm_zero, mul_zero]
      positivity
    by_cases ha : Ψ (a4 0 v₁ v₂ v₃ β).2 = 0
    · rw [ha, norm_zero, zero_mul, zero_mul]
      positivity
    have hcB := Ratio_c_le_PL hN h₁ h₂ h₃ (Ratio_inM hb) (Ratio_inM ha)
    have hgβ : g β = ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ ^ 2 := by simp [g, hc]
    rw [hgβ]
    have h2 := two_mul_le_add_sq ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ ‖Ψ β‖
    calc ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖
        ≤ ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * B * ‖Ψ β‖ := by gcongr
      _ = B / 2 * (2 * ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * ‖Ψ β‖) := by ring
      _ ≤ _ := by gcongr
  have hsum : Summable fun β => B / 2 * (g β + ‖Ψ β‖ ^ 2) := (hgs.add hs).mul_left _
  have hnn : ∀ β, 0 ≤ ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖ := fun β => by
    have := a4_fst_nonneg 0 v₁ v₂ v₃ β
    positivity
  unfold OneLeg_absA
  calc (∑' β, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖)
      ≤ ∑' β, B / 2 * (g β + ‖Ψ β‖ ^ 2) :=
        (Summable.of_nonneg_of_le hnn hterm hsum).tsum_le_tsum hterm hsum
    _ = B / 2 * ((∑' β, g β) + ∑' β, ‖Ψ β‖ ^ 2) := by
        rw [tsum_mul_left, hgs.tsum_add hs]
    _ ≤ B / 2 * ((∑' γ, ‖Ψ γ‖ ^ 2) + ∑' β, ‖Ψ β‖ ^ 2) := by gcongr
    _ = B := by rw [hΨ.1.tsum_eq]; ring

/-- From `c z² t² ≤ r² P q²` with `P ≤ M³` to `t ≤ r (c⁻¹ + 1) M² z⁻¹ q`. -/
private lemma Ratio_alg34 {t r c M P q z : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hc : 0 < c)
    (hM : 1 ≤ M) (hP : P ≤ M ^ 3) (hq : 0 ≤ q) (hz : 0 < z)
    (h : c * z ^ 2 * t ^ 2 ≤ r ^ 2 * P * q ^ 2) :
    t ≤ r * (c⁻¹ + 1) * M ^ 2 * (z⁻¹ * q) := by
  have h1 : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
  have h2 : 1 ≤ (c⁻¹ + 1) ^ 2 * c := by
    have e : (c⁻¹ + 1) ^ 2 * c = c⁻¹ + 2 + c := by field_simp; ring
    rw [e]
    have := inv_pos.2 hc
    linarith
  have key : c * z ^ 2 * t ^ 2 ≤ c * z ^ 2 * (r * (c⁻¹ + 1) * M ^ 2 * (z⁻¹ * q)) ^ 2 := by
    calc c * z ^ 2 * t ^ 2 ≤ r ^ 2 * P * q ^ 2 := h
      _ ≤ r ^ 2 * M ^ 3 * q ^ 2 := by gcongr
      _ ≤ r ^ 2 * M ^ 4 * q ^ 2 := by gcongr
      _ = r ^ 2 * M ^ 4 * q ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * M ^ 4 * q ^ 2 * ((c⁻¹ + 1) ^ 2 * c) := by gcongr
      _ = c * z ^ 2 * (r * (c⁻¹ + 1) * M ^ 2 * (z⁻¹ * q)) ^ 2 := by field_simp
  have := le_of_mul_le_mul_left key (by positivity)
  exact (pow_le_pow_iff_left₀ ht (by positivity) (by norm_num)).1 this

/-- A state with `F(γ) = 1` is asymmetric at one of the legs, (3.9) [defMsau]. -/
private lemma Ratio_Fal_one {ρ L : ℝ} {v₁ v₂ v₃ : Idx} {γ : Occ}
    (h : Fal ρ L ![v₁, v₂, v₃] γ = 1) :
    γ v₁ ≠ γ (-v₁) ∨ γ v₂ ≠ γ (-v₂) ∨ γ v₃ ≠ γ (-v₃) := by
  by_contra hcon
  simp only [not_or, ne_eq, not_not] at hcon
  obtain ⟨e1, e2, e3⟩ := hcon
  have : Fal ρ L ![v₁, v₂, v₃] γ = 0 := by
    unfold Fal
    simp [Fin.sum_univ_three, e1, e2, e3]
  omega

/-- The final count of (8.34) in powers of `t = ε`. -/
private lemma Ratio_fin34 {t g C x : ℝ} (t0 : 0 < t) (t1 : t ≤ 1) (hg : 0 < g) (hC : 0 ≤ C)
    (hx0 : 0 ≤ x) (hx : x ≤ t ^ 200) :
    2 * ((t ^ 10)⁻¹ * ((g / 2 * t ^ 2)⁻¹ + 1) ^ 2 * (t⁻¹ + 2) ^ 2) *
        (x + 3 * (C * t ^ 200 * t⁻¹ / t)) ≤
      18 * (2 / g + 1) ^ 2 * (1 + 3 * C) * t ^ 180 := by
  have ha : ((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2 ≤ 2 / g + 1 := by
    have e : ((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2 = 2 / g + t ^ 2 := by field_simp
    rw [e]
    nlinarith [pow_le_one₀ t0.le t1 (n := 2)]
  have hb : (t⁻¹ + 2) * t ≤ 3 := by
    have e : (t⁻¹ + 2) * t = 1 + 2 * t := by field_simp
    rw [e]
    linarith
  have hy : x + 3 * (C * t ^ 200 * t⁻¹ / t) ≤ (1 + 3 * C) * t ^ 198 := by
    have e : C * t ^ 200 * t⁻¹ / t = C * t ^ 198 := by field_simp
    have : t ^ 200 ≤ t ^ 198 := pow_le_pow_of_le_one t0.le t1 (by norm_num)
    rw [e]
    nlinarith
  have e : 2 * ((t ^ 10)⁻¹ * ((g / 2 * t ^ 2)⁻¹ + 1) ^ 2 * (t⁻¹ + 2) ^ 2) *
        (x + 3 * (C * t ^ 200 * t⁻¹ / t)) =
      2 * (((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2) ^ 2 * ((t⁻¹ + 2) * t) ^ 2 *
        (x + 3 * (C * t ^ 200 * t⁻¹ / t)) * (t ^ 16)⁻¹ := by
    field_simp
  rw [e]
  have h0a : 0 ≤ ((g / 2 * t ^ 2)⁻¹ + 1) * t ^ 2 := by positivity
  have h0b : 0 ≤ (t⁻¹ + 2) * t := by positivity
  calc _ ≤ 2 * (2 / g + 1) ^ 2 * 3 ^ 2 * ((1 + 3 * C) * t ^ 198) * (t ^ 16)⁻¹ := by gcongr
    _ = 18 * (2 / g + 1) ^ 2 * (1 + 3 * C) * (t ^ 198 * (t ^ 16)⁻¹) := by ring
    _ = 18 * (2 / g + 1) ^ 2 * (1 + 3 * C) * t ^ 182 := by
        rw [← pow_sub₀ _ t0.ne' (by norm_num)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t0.le t1 (by norm_num))
        (by positivity)

/-- The branch `F(α) ≤ 1` of (8.33)–(8.34), from (8.12) [fal0]. -/
private lemma Ratio_br34a {n ρ l₁ l₂ l₃ c₀ T A P r M : ℝ} {Fa Fb : ℕ} (hn : 0 < n)
    (hρ : 0 < ρ) (hl₂ : 0 ≤ l₂) (hl₃ : 0 ≤ l₃) (hc₀ : 0 < c₀) (ha₁ : c₀ ≤ ρ * l₁)
    (ha₂ : ρ * l₂ ≤ 1) (ha₃ : ρ * l₃ ≤ 1) (hT : 0 ≤ T) (hr : 0 ≤ r) (hM : 1 ≤ M)
    (hP0 : 0 ≤ P) (hP : P ≤ M ^ 3) (hF : Fa + Fb = 3) (hFa : Fa ≤ 1)
    (h : n ^ Fb * l₁ * T ^ 2 ≤ r ^ 2 * n ^ (Fa + 1) * (ρ * (l₂ * l₃)) * P * A ^ 4) :
    T ≤ r * (c₀⁻¹ + 1) * M ^ 2 * ((n ^ (1 - Fa))⁻¹ * A ^ 2) := by
  have hz : 0 < n ^ (1 - Fa) := pow_pos hn _
  have hNz : n ^ (Fa + 1) * (n ^ (1 - Fa)) ^ 2 = n ^ Fb := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  refine Ratio_alg34 hT hr hc₀ hM hP (by positivity) hz ?_
  refine le_of_mul_le_mul_left ?_ (pow_pos hn (Fa + 1))
  have hb : 0 ≤ ρ * l₂ := by positivity
  have hc : 0 ≤ ρ * l₃ := by positivity
  calc n ^ (Fa + 1) * (c₀ * (n ^ (1 - Fa)) ^ 2 * T ^ 2)
      ≤ n ^ (Fa + 1) * ((ρ * l₁) * (n ^ (1 - Fa)) ^ 2 * T ^ 2) := by gcongr
    _ = ρ * (n ^ Fb * l₁ * T ^ 2) := by rw [← hNz]; ring
    _ ≤ ρ * (r ^ 2 * n ^ (Fa + 1) * (ρ * (l₂ * l₃)) * P * A ^ 4) := by gcongr
    _ = n ^ (Fa + 1) * (r ^ 2 * ((ρ * l₂) * (ρ * l₃)) * P * (A ^ 2) ^ 2) := by ring
    _ ≤ n ^ (Fa + 1) * (r ^ 2 * (1 * 1) * P * (A ^ 2) ^ 2) := by gcongr
    _ = n ^ (Fa + 1) * (r ^ 2 * P * (A ^ 2) ^ 2) := by ring

/-- The branch `F(β) ≤ 1` of (8.33)–(8.34), from (8.13) [fbe0]. -/
private lemma Ratio_br34b {n ρ l₁ l₂ l₃ c₀ T B P r M : ℝ} {Fa Fb : ℕ} (hn : 0 < n)
    (hρ : 0 < ρ) (hc₀ : 0 < c₀) (ha₁ : ρ * l₁ ≤ 1) (ha₂ : c₀ ≤ ρ * l₂)
    (ha₃ : c₀ ≤ ρ * l₃) (hT : 0 ≤ T) (hr : 0 ≤ r) (hM : 1 ≤ M)
    (hP0 : 0 ≤ P) (hP : P ≤ M ^ 3) (hF : Fa + Fb = 3) (hFb : Fb ≤ 1)
    (h : n ^ Fa * (ρ * (l₂ * l₃)) * T ^ 2 ≤ r ^ 2 * n ^ (Fb + 1) * l₁ * P * B ^ 4) :
    T ≤ r * ((c₀ ^ 2)⁻¹ + 1) * M ^ 2 * ((n ^ (1 - Fb))⁻¹ * B ^ 2) := by
  have hz : 0 < n ^ (1 - Fb) := pow_pos hn _
  have hNz : n ^ (Fb + 1) * (n ^ (1 - Fb)) ^ 2 = n ^ Fa := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  refine Ratio_alg34 hT hr (by positivity) hM hP (by positivity) hz ?_
  refine le_of_mul_le_mul_left ?_ (pow_pos hn (Fb + 1))
  have hc2 : c₀ ^ 2 ≤ (ρ * l₂) * (ρ * l₃) := by
    rw [sq]
    exact mul_le_mul ha₂ ha₃ hc₀.le (hc₀.le.trans ha₂)
  calc n ^ (Fb + 1) * (c₀ ^ 2 * (n ^ (1 - Fb)) ^ 2 * T ^ 2)
      ≤ n ^ (Fb + 1) * (((ρ * l₂) * (ρ * l₃)) * (n ^ (1 - Fb)) ^ 2 * T ^ 2) := by gcongr
    _ = ρ * (n ^ Fa * (ρ * (l₂ * l₃)) * T ^ 2) := by rw [← hNz]; ring
    _ ≤ ρ * (r ^ 2 * n ^ (Fb + 1) * l₁ * P * B ^ 4) := by gcongr
    _ = n ^ (Fb + 1) * (r ^ 2 * (ρ * l₁) * P * (B ^ 2) ^ 2) := by ring
    _ ≤ n ^ (Fb + 1) * (r ^ 2 * 1 * P * (B ^ 2) ^ 2) := by gcongr
    _ = n ^ (Fb + 1) * (r ^ 2 * P * (B ^ 2) ^ 2) := by ring

/-- One summand of `Σ_β |Ψ(α)| ⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ |Ψ(β)|` in case (8.4)
[one0thirdcase]: the bound by `H(T β) + H(β)` of (8.33)–(8.34). -/
private lemma Ratio_term34 {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN1 : 1 ≤ N) {v₁ v₂ v₃ : Idx}
    (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (hp₁₂ : Legs_pm v₁ v₂) (hp₁₃ : Legs_pm v₁ v₃)
    (hp₂₃ : Legs_pm v₂ v₃) {c₀ r : ℝ} (hc₀ : 0 < c₀) (hr0 : 0 ≤ r)
    (hr2 : rhoN N ^ (-(1 / 10 : ℝ)) = r ^ 2)
    (ha : ∀ u, inPL (rhoN N) (LN N) u → c₀ ≤ rhoN N * |lam V w (rhoN N) (LN N) u| ∧
      rhoN N * |lam V w (rhoN N) (LN N) u| ≤ 1)
    (h12 : ∀ α β : Occ, InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β * |lam V w (rhoN N) (LN N) v₁| *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α + 1) *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          ((α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 4)
    (h13 : ∀ α β : Occ, InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 0 v₁ v₂ v₃ β).1 ≠ 0 → (a4 0 v₁ v₂ v₃ β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α *
          (rhoN N * |lam V w (rhoN N) (LN N) v₂ * lam V w (rhoN N) (LN N) v₃|) *
          (‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖) ^ 2 ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β + 1) *
          |lam V w (rhoN N) (LN N) v₁| *
          (((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ)) * ‖trialState V w kc N β‖ ^ 4)
    {H : Occ → ℝ} (hH0 : ∀ γ, 0 ≤ H γ)
    (hHge : ∀ γ, InM (rhoN N) (LN N) kc N γ → Fal (rhoN N) (LN N) ![v₁, v₂, v₃] γ ≤ 1 →
      ((N : ℝ) ^ (1 - Fal (rhoN N) (LN N) ![v₁, v₂, v₃] γ))⁻¹ * ‖trialState V w kc N γ‖ ^ 2 ≤
        H γ)
    (β : Occ) :
    ‖trialState V w kc N (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 *
        ‖trialState V w kc N β‖ ≤
      r * (c₀⁻¹ + 1) ^ 2 * (mc (rhoN N) + 2) ^ 2 *
        ((if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then H (a4 0 v₁ v₂ v₃ β).2 else 0) + H β) := by
  have hρ := (Particles_rhoN_LN hN1).2.1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN1
  have hM1 : 1 ≤ mc (rhoN N) + 2 := by
    have : 0 ≤ mc (rhoN N) := by unfold mc rhoN; positivity
    linarith
  have hHβ := hH0 β
  have hR0 : 0 ≤ r * (c₀⁻¹ + 1) ^ 2 * (mc (rhoN N) + 2) ^ 2 := by positivity
  have hocc : ∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → ∀ u, inPL (rhoN N) (LN N) u →
      (γ u : ℝ) + 1 ≤ mc (rhoN N) + 2 := fun γ hγ u hu => by
    have := ((Nat.cast_le.2 (le_max_left _ _)).trans_lt (MStar_PL_mc hρ hγ hu)).le
    linarith
  by_cases hc : (a4 0 v₁ v₂ v₃ β).1 = 0
  · rw [hc, mul_zero, zero_mul]
    simp only [ne_eq, not_true_eq_false, ite_false, zero_add]
    positivity
  by_cases hb : trialState V w kc N β = 0
  · rw [hb, norm_zero, mul_zero]
    have : 0 ≤ (if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then H (a4 0 v₁ v₂ v₃ β).2 else 0) := by
      split_ifs <;> simp [hH0]
    positivity
  by_cases hav : trialState V w kc N (a4 0 v₁ v₂ v₃ β).2 = 0
  · rw [hav, norm_zero, zero_mul, zero_mul]
    have : 0 ≤ (if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then H (a4 0 v₁ v₂ v₃ β).2 else 0) := by
      split_ifs <;> simp [hH0]
    positivity
  simp only [ne_eq, hc, not_false_eq_true, ite_true]
  generalize hα_def : (a4 0 v₁ v₂ v₃ β).2 = α at hav ⊢
  have hαM := Ratio_inM hav
  have hβM := Ratio_inM hb
  have h0₁ := Regions_PL_ne_zero hρ h₁
  have h0₂ := Regions_PL_ne_zero hρ h₂
  have h0₃ := Regions_PL_ne_zero hρ h₃
  have hF := Lemma8_2_F hρ h0₁ h0₂ h0₃ hp₁₂ hp₁₃ hp₂₃ hαM hβM hc hα_def
  have hcard : ({i | inPL (rhoN N) (LN N) (![v₁, v₂, v₃] i)} : Finset (Fin 3)).card = 3 := by
    rw [Finset.card_filter, Fin.sum_univ_three]
    simp [h₁, h₂, h₃]
  rw [hcard] at hF
  have hT0 : 0 ≤ ‖trialState V w kc N α‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖trialState V w kc N β‖ := by
    have := a4_fst_nonneg 0 v₁ v₂ v₃ β
    positivity
  obtain ⟨ha₁, ha₁'⟩ := ha v₁ h₁
  obtain ⟨ha₂, ha₂'⟩ := ha v₂ h₂
  obtain ⟨ha₃, ha₃'⟩ := ha v₃ h₃
  rcases le_or_gt (Fal (rhoN N) (LN N) ![v₁, v₂, v₃] α) 1 with hFα | hFα
  · have h := h12 α β hαM hβM hc hα_def
    rw [hr2, abs_mul] at h
    have hP : (α v₁ : ℝ) * ((α v₂ : ℝ) + 1) * ((α v₃ : ℝ) + 1) ≤ (mc (rhoN N) + 2) ^ 3 := by
      have e1 := hocc α hαM v₁ h₁
      have e2 := hocc α hαM v₂ h₂
      have e3 := hocc α hαM v₃ h₃
      rw [show (mc (rhoN N) + 2) ^ 3 = (mc (rhoN N) + 2) * (mc (rhoN N) + 2) *
        (mc (rhoN N) + 2) by ring]
      have : (α v₁ : ℝ) ≤ mc (rhoN N) + 2 := by linarith
      gcongr
    have hfin := Ratio_br34a hn hρ (abs_nonneg _) (abs_nonneg _) hc₀ ha₁ ha₂' ha₃' hT0 hr0 hM1
      (by positivity) hP hF hFα h
    have hHα := hHge α hαM hFα
    have hc1 : c₀⁻¹ + 1 ≤ (c₀⁻¹ + 1) ^ 2 := by
      have := inv_pos.2 hc₀
      nlinarith
    calc _ ≤ _ := hfin
      _ ≤ r * (c₀⁻¹ + 1) ^ 2 * (mc (rhoN N) + 2) ^ 2 * H α := by gcongr
      _ ≤ _ := by gcongr; linarith
  · have hFβ : Fal (rhoN N) (LN N) ![v₁, v₂, v₃] β ≤ 1 := by omega
    have h := h13 α β hαM hβM hc hα_def
    rw [hr2, abs_mul] at h
    have hP : ((β v₁ : ℝ) + 1) * (β v₂ : ℝ) * (β v₃ : ℝ) ≤ (mc (rhoN N) + 2) ^ 3 := by
      have e1 := hocc β hβM v₁ h₁
      have e2 := hocc β hβM v₂ h₂
      have e3 := hocc β hβM v₃ h₃
      rw [show (mc (rhoN N) + 2) ^ 3 = (mc (rhoN N) + 2) * (mc (rhoN N) + 2) *
        (mc (rhoN N) + 2) by ring]
      have : (β v₂ : ℝ) ≤ mc (rhoN N) + 2 := by linarith
      have : (β v₃ : ℝ) ≤ mc (rhoN N) + 2 := by linarith
      gcongr
    have hfin := Ratio_br34b hn hρ hc₀ ha₁' ha₂ ha₃ hT0 hr0 hM1
      (by positivity) hP hF hFβ h
    have hHβ' := hHge β hβM hFβ
    have hc2 : (c₀ ^ 2)⁻¹ + 1 ≤ (c₀⁻¹ + 1) ^ 2 := by
      have := inv_pos.2 hc₀
      rw [← inv_pow]
      nlinarith
    calc _ ≤ _ := hfin
      _ ≤ r * (c₀⁻¹ + 1) ^ 2 * (mc (rhoN N) + 2) ^ 2 * H β := by gcongr
      _ ≤ _ := by gcongr; linarith [hH0 α]

/-- (8.33)–(8.34) for one pair in case (8.4) [one0thirdcase] with `v_i ≠ ±v_j`. -/
theorem Eq8_34 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ v₁ v₂ : Idx,
      OneLeg_case3 (rhoN N) (LN N) v₁ v₂ → Legs_pm v₁ v₂ → Legs_pm v₁ (v₁ - v₂) →
      Legs_pm v₂ (v₁ - v₂) →
      OneLeg_absA (trialState V w kc N) v₁ v₂ (v₁ - v₂) ≤ C * rhoN N ^ (1 - 1/10 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨N₁, h12⟩ := Eq8_12 hV hw
  obtain ⟨N₂, h13⟩ := Eq8_13 hV hw
  obtain ⟨C₃, hC₃, N₃, h23⟩ := Eq5_23 V w
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop (max (max N₁ N₂) (max N₃ 1))).and
      ((Ratio_ev_lam hV hw).and (Ratio_ev_eps (δ := 1 / 2) (by norm_num))))
  refine ⟨18 * (2 / g0 V w + 1) ^ 2 * (1 + 3 * C₃), by positivity, N₀,
    fun N hN kc v₁ v₂ hcase hp₁₂ hp₁₃ hp₂₃ => ?_⟩
  obtain ⟨hNmax, hl, hε⟩ := hN₀ N hN
  have hNN₁ : N ≥ N₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNmax
  have hNN₂ : N ≥ N₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNmax
  have hNN₃ : N ≥ N₃ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNmax
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNmax
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨h₁, h₂, h₃⟩ := hcase
  set v₃ := v₁ - v₂ with hv₃
  have h0₁ := Regions_PL_ne_zero hρ h₁
  have h0₂ := Regions_PL_ne_zero hρ h₂
  have h0₃ := Regions_PL_ne_zero hρ h₃
  set t := epsP (rhoN N) with ht_def
  have t0 : 0 < t := by rw [ht_def, epsP]; positivity
  have t1 : t ≤ 1 := hε.trans (by norm_num)
  have hΨ := Normalization_isNState V w kc hN1
  set Ψ := trialState V w kc N with hΨ_def
  set c₀ := g0 V w / 2 * t ^ 2 with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  set r := (t ^ 10)⁻¹ with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr2 : rhoN N ^ (-(1 / 10 : ℝ)) = r ^ 2 := by
    rw [Ratio_rpow_eps_neg hρ.le 20 (by norm_num), hr_def, inv_pow, ← pow_mul]
  have hmc : mc (rhoN N) = t⁻¹ := Ratio_mc hρ.le
  set M := mc (rhoN N) + 2 with hM_def
  have ha : ∀ u, inPL (rhoN N) (LN N) u →
      c₀ ≤ rhoN N * |lam V w (rhoN N) (LN N) u| ∧ rhoN N * |lam V w (rhoN N) (LN N) u| ≤ 1 := by
    intro u hu
    have h1 := Ratio_hlam hV hw hN1 hl u hu
    have h2 := (scat_lam_PL hV hw _ hρ _ u hu).2
    rw [abs_of_neg h2, mul_neg]
    exact h1
  set I : Idx → Occ → ℝ := fun u γ =>
    if InMuA (rhoN N) (LN N) kc N u γ then ‖Ψ γ‖ ^ 2 else 0 with hI_def
  set H : Occ → ℝ := fun γ => (N : ℝ)⁻¹ * ‖Ψ γ‖ ^ 2 + I v₁ γ + I v₂ γ + I v₃ γ with hH_def
  have hI0 : ∀ u γ, 0 ≤ I u γ := fun u γ => by simp only [hI_def]; split_ifs <;> positivity
  have hH0 : ∀ γ, 0 ≤ H γ := fun γ => by
    have := hI0 v₁ γ; have := hI0 v₂ γ; have := hI0 v₃ γ
    simp only [hH_def]
    positivity
  have hHge : ∀ γ, InM (rhoN N) (LN N) kc N γ → Fal (rhoN N) (LN N) ![v₁, v₂, v₃] γ ≤ 1 →
      ((N : ℝ) ^ (1 - Fal (rhoN N) (LN N) ![v₁, v₂, v₃] γ))⁻¹ * ‖Ψ γ‖ ^ 2 ≤ H γ := by
    intro γ hγ hF
    have := hI0 v₁ γ; have := hI0 v₂ γ; have := hI0 v₃ γ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hF with hF0 | hF1
    · rw [hF0, Nat.sub_zero, pow_one, hH_def]
      dsimp only
      linarith
    · rw [hF1, Nat.sub_self, pow_zero, inv_one, one_mul, hH_def]
      dsimp only
      have := (sq_nonneg ‖Ψ γ‖)
      rcases Ratio_Fal_one hF1 with e | e | e
      · have : I v₁ γ = ‖Ψ γ‖ ^ 2 := by
          simp only [hI_def, InMuA, hγ, ne_eq, e, not_false_eq_true, and_self, ite_true]
        nlinarith [inv_nonneg.2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      · have : I v₂ γ = ‖Ψ γ‖ ^ 2 := by
          simp only [hI_def, InMuA, hγ, ne_eq, e, not_false_eq_true, and_self, ite_true]
        nlinarith [inv_nonneg.2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      · have : I v₃ γ = ‖Ψ γ‖ ^ 2 := by
          simp only [hI_def, InMuA, hγ, ne_eq, e, not_false_eq_true, and_self, ite_true]
        nlinarith [inv_nonneg.2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  set G : Occ → ℝ := fun β =>
    if (a4 0 v₁ v₂ v₃ β).1 ≠ 0 then H (a4 0 v₁ v₂ v₃ β).2 else 0 with hG_def
  set R := r * (c₀⁻¹ + 1) ^ 2 * M ^ 2 with hR_def
  have hR0 : 0 ≤ R := by positivity
  have hterm : ∀ β, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖ ≤
      R * (G β + H β) := fun β =>
    Ratio_term34 hN1 h₁ h₂ h₃ hp₁₂ hp₁₃ hp₂₃ hc₀ hr0 hr2 ha
      (fun α β => h12 N hNN₁ kc α β v₁ v₂ v₃ h0₁ h0₂ h0₃ hp₁₂ hp₁₃ hp₂₃)
      (fun α β => h13 N hNN₂ kc α β v₁ v₂ v₃ h0₁ h0₂ h0₃ hp₁₂ hp₁₃ hp₂₃) hH0 hHge β
  have hs : Summable fun γ => ‖Ψ γ‖ ^ 2 := hΨ.1.summable
  have hIs : ∀ u, Summable (I u) := fun u =>
    Summable.of_nonneg_of_le (hI0 u) (fun γ => by simp only [hI_def]; split_ifs <;> simp) hs
  have hHs : Summable H :=
    (((hs.mul_left _).add (hIs v₁)).add (hIs v₂)).add (hIs v₃)
  obtain ⟨hGs, hGle⟩ := Ratio_reindex 0 v₁ v₂ v₃ hH0 hHs
  have hHsum : ∑' γ, H γ ≤ (N : ℝ)⁻¹ + 3 * (C₃ * rhoN N * mc (rhoN N) / epsP (rhoN N)) := by
    have e : ∑' γ, H γ = (N : ℝ)⁻¹ * (∑' γ, ‖Ψ γ‖ ^ 2) + (∑' γ, I v₁ γ) + (∑' γ, I v₂ γ) +
        (∑' γ, I v₃ γ) := by
      simp only [hH_def]
      rw [(((hs.mul_left _).add (hIs v₁)).add (hIs v₂)).tsum_add (hIs v₃),
        ((hs.mul_left _).add (hIs v₁)).tsum_add (hIs v₂), (hs.mul_left _).tsum_add (hIs v₁),
        tsum_mul_left]
    rw [e, hΨ.1.tsum_eq]
    have := h23 N hNN₃ kc v₁ h₁
    have := h23 N hNN₃ kc v₂ h₂
    have := h23 N hNN₃ kc v₃ h₃
    simp only [hI_def]
    linarith
  have hsum : Summable fun β => R * (G β + H β) := (hGs.add hHs).mul_left _
  have hnn : ∀ β, 0 ≤ ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖ := fun β => by
    have := a4_fst_nonneg 0 v₁ v₂ v₃ β
    positivity
  unfold OneLeg_absA
  calc (∑' β, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖)
      ≤ ∑' β, R * (G β + H β) :=
        (Summable.of_nonneg_of_le hnn hterm hsum).tsum_le_tsum hterm hsum
    _ = R * ((∑' β, G β) + ∑' β, H β) := by rw [tsum_mul_left, hGs.tsum_add hHs]
    _ ≤ R * ((∑' γ, H γ) + ∑' β, H β) := by gcongr
    _ ≤ 2 * R * ((N : ℝ)⁻¹ + 3 * (C₃ * rhoN N * mc (rhoN N) / epsP (rhoN N))) := by
        have := hH0
        nlinarith
    _ ≤ _ := by
        have hx := Ratio_inv_N_le hN1
        rw [Ratio_rho_eps hρ.le] at hx
        rw [hR_def, hM_def, hmc, hc₀_def, hr_def, Ratio_rpow_eps hρ.le 180 (by norm_num),
          ← ht_def]
        conv_lhs => rw [Ratio_rho_eps hρ.le]
        rw [← ht_def]
        exact Ratio_fin34 t0 t1 hg hC₃ (by positivity) hx

end LHYUpper
