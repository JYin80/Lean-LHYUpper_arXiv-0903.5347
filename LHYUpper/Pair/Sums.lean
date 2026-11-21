module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Particles.Basic
public import LHYUpper.Riemann.Bridge
public import LHYUpper.Riemann.ScaledLimits
public import LHYUpper.Scattering.Identities
public import LHYUpper.Pair.Identities

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Scaling facts at `ρ = ρ_N`, `L = L_N` -/

/-- `ρ_N → 0` through positive values. -/
private lemma Sums_tendsto_rho : Tendsto rhoN atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8 / 17)).comp
      tendsto_natCast_atTop_atTop
  · filter_upwards [eventually_ge_atTop 1] with N hN using (Particles_rhoN_LN hN).2.1

/-- `ρ_N^{-a} → ∞` for `a > 0`. -/
private lemma Sums_tendsto_rho_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ (-a)) atTop atTop := by
  have h := (tendsto_rpow_atTop (mul_pos (by norm_num : (0 : ℝ) < 8 / 17) ha)).comp
    tendsto_natCast_atTop_atTop
  refine Tendsto.congr (fun N => ?_) h
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

/-- `ρ_N^b → 0` for `b > 0`. -/
private lemma Sums_tendsto_rho_pow {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => rhoN N ^ b) atTop (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).tendsto
  rw [Real.zero_rpow hb.ne'] at h
  exact h.comp (tendsto_nhdsWithin_iff.1 Sums_tendsto_rho).1

/-- `2π ≤ L_N` for `N` large. -/
private lemma Sums_eventually_L : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N := by
  have h := (Sums_tendsto_rho_neg (by norm_num : (0 : ℝ) < 25 / 24)).eventually_ge_atTop (2 * π)
  filter_upwards [h] with N hN using hN

/-- The rate `E₂(δ) = δ (1 + log δ⁻¹)` is at most `3 δ^{1/2}` for `0 < δ ≤ 1`. -/
private lemma Sums_rate_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    riemannRate 2 δ ≤ 3 * δ ^ (1 / 2 : ℝ) := by
  have hs : 0 < δ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hsq : δ ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ) = δ := by
    rw [← Real.rpow_add hδ]
    norm_num
  have hs1 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hlog : Real.log δ⁻¹ ≤ 2 * (δ ^ (1 / 2 : ℝ))⁻¹ := by
    have h := Real.log_le_rpow_div (inv_nonneg.2 hδ.le) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.inv_rpow hδ.le] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  have e : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by simp [riemannRate]
  rw [e]
  generalize δ ^ (1 / 2 : ℝ) = s at hs hsq hs1 hlog ⊢
  calc δ * (1 + Real.log δ⁻¹) ≤ δ * (1 + 2 * s⁻¹) := by gcongr
    _ = s * s + 2 * s := by
        rw [← hsq]
        field_simp
    _ ≤ 3 * s := by nlinarith

/-- `E₂(c ρ^κ) ≤ 3 c^{1/2} ρ^b` for `b ≤ κ/2`, `0 < ρ ≤ 1` and `c ρ^κ ≤ 1`. -/
private lemma Sums_rate_pow {c κ b ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hb : b ≤ κ / 2) (hδ : c * ρ ^ κ ≤ 1) :
    riemannRate 2 (c * ρ ^ κ) ≤ 3 * c ^ (1 / 2 : ℝ) * ρ ^ b := by
  have h := Sums_rate_le (by positivity) hδ
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le] at h
  have h2 : ρ ^ (κ * (1 / 2 : ℝ)) ≤ ρ ^ b :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have hc2 : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc.le _
  calc riemannRate 2 (c * ρ ^ κ) ≤ 3 * (c ^ (1 / 2 : ℝ) * ρ ^ (κ * (1 / 2 : ℝ))) := h
    _ ≤ 3 * (c ^ (1 / 2 : ℝ) * ρ ^ b) := by gcongr
    _ = 3 * c ^ (1 / 2 : ℝ) * ρ ^ b := by ring

/-- `2π / L_N = 2π ρ_N^{25/24}`. -/
private lemma Sums_two_pi_div_L {N : ℕ} (hN : 1 ≤ N) :
    2 * π / LN N = 2 * π * rhoN N ^ (25 / 24 : ℝ) := by
  have hρ := (Particles_rhoN_LN hN).2.1
  rw [LN, Real.rpow_neg hρ.le, div_inv_eq_mul]

/-- `L_N ρ_N^b = ρ_N^{b − 25/24}`. -/
private lemma Sums_L_mul_rpow {N : ℕ} (hN : 1 ≤ N) (b : ℝ) :
    LN N * rhoN N ^ b = rhoN N ^ (b - 25 / 24) := by
  have hρ := (Particles_rhoN_LN hN).2.1
  rw [LN, ← Real.rpow_add hρ]
  congr 1
  ring

/-- Rate at the lattice spacing `2π/L_N`. -/
private lemma Sums_rate_LN {N : ℕ} (hN : 1 ≤ N) (hL : 2 * π ≤ LN N) {b : ℝ} (hb : b ≤ 25 / 48) :
    riemannRate 2 (2 * π / LN N) ≤ 3 * (2 * π) ^ (1 / 2 : ℝ) * rhoN N ^ b := by
  obtain ⟨-, hρ, hρ1, hLpos⟩ := Particles_rhoN_LN hN
  have hδ : 2 * π * rhoN N ^ (25 / 24 : ℝ) ≤ 1 := by
    rw [← Sums_two_pi_div_L hN, div_le_one hLpos]
    exact hL
  rw [Sums_two_pi_div_L hN]
  exact Sums_rate_pow (by positivity) hρ hρ1 (by linarith) hδ

/-- Rate at the scaled spacing `2π/(L_N ρ_N^{1/2})`. -/
private lemma Sums_rate_PL {N : ℕ} (hN : 1 ≤ N) (hL : 2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ))
    {b : ℝ} (hb : b ≤ 13 / 48) :
    riemannRate 2 (2 * π / (LN N * rhoN N ^ (1 / 2 : ℝ))) ≤
      3 * (2 * π) ^ (1 / 2 : ℝ) * rhoN N ^ b := by
  obtain ⟨-, hρ, hρ1, hLpos⟩ := Particles_rhoN_LN hN
  have hpos : 0 < LN N * rhoN N ^ (1 / 2 : ℝ) := by positivity
  have e : 2 * π / (LN N * rhoN N ^ (1 / 2 : ℝ)) = 2 * π * rhoN N ^ (13 / 24 : ℝ) := by
    rw [Sums_L_mul_rpow hN, show (1 / 2 : ℝ) - 25 / 24 = -(13 / 24) by norm_num,
      Real.rpow_neg hρ.le, div_inv_eq_mul]
  have hδ : 2 * π * rhoN N ^ (13 / 24 : ℝ) ≤ 1 := by
    rw [← e, div_le_one hpos]
    exact hL
  rw [e]
  exact Sums_rate_pow (by positivity) hρ hρ1 (by linarith) hδ


/-- `(2π)^{-3} ∫ V_p w_p = ‖Vw‖₁`, for `V_p = Re V̂_p`, `w_p = Re ĝ_p |p|^{-2}`. -/
private lemma Sums_int_Vw {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ((2 * π) ^ 3)⁻¹ * ∫ p : R3, (ft V p).re * ((ft (gfun V w) p).re / ‖p‖ ^ 2) =
      normVw V w := by
  have e : normVw V w = ∫ x, V x * w x := by
    unfold normVw
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact abs_of_nonneg (mul_nonneg (hV.nonneg x) (hw.nonneg x))
  rw [e, scat_Vw_eq hV hw, ← inv_pow]
  rfl

/-- `(2π)^{-6} ∫∫ V_{p−q} w_p w_q = ‖Vw²‖₁`. -/
private lemma Sums_int_Vww {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    (((2 * π) ^ 3) ^ 2)⁻¹ * ∫ p : R3, ∫ q : R3,
      (ft V (p - q)).re * ((ft (gfun V w) p).re / ‖p‖ ^ 2) * ((ft (gfun V w) q).re / ‖q‖ ^ 2) =
      normVw2 V w := by
  have e : normVw2 V w = ∫ x, V x * w x ^ 2 := by
    unfold normVw2
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact abs_of_nonneg (mul_nonneg (hV.nonneg x) (sq_nonneg _))
  rw [e, scat_Vw2_eq hV hw, ← pow_mul, ← inv_pow]
  rfl

/-! ### Regions and lattice points -/

/-- `ε_P(ρ)² = ρ^{1/100}`. -/
private lemma Sums_eps_sq {ρ : ℝ} (hρ : 0 ≤ ρ) : epsP ρ ^ 2 = ρ ^ (1 / 100 : ℝ) := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ]
  norm_num

/-- `ε_P(ρ) > 0` for `ρ > 0`. -/
private lemma Sums_eps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _

/-- `ε⁻¹ ρ^{1/2} = ρ^{1/2 − 1/200}`. -/
private lemma Sums_R_eq {ρ : ℝ} (hρ : 0 < ρ) :
    (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) = ρ ^ (1 / 2 - 1 / 200 : ℝ) := by
  rw [epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
  congr 1
  ring

/-- `ε ρ^{1/2} = ρ^{1/2 + 1/200}`. -/
private lemma Sums_r1_eq {ρ : ℝ} (hρ : 0 < ρ) :
    epsP ρ * ρ ^ (1 / 2 : ℝ) = ρ ^ (1 / 2 + 1 / 200 : ℝ) := by
  rw [epsP, ← Real.rpow_add hρ]
  congr 1
  ring

/-- `ε ρ^{1/2} ≤ ε⁻¹ ρ^{1/2}`. -/
private lemma Sums_r1_le_R {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    epsP ρ * ρ ^ (1 / 2 : ℝ) ≤ (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) := by
  rw [Sums_r1_eq hρ, Sums_R_eq hρ]
  exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)

/-- `ε⁻¹ ρ^{1/2} ≤ ε`. -/
private lemma Sums_R_le_eps {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) ≤ epsP ρ := by
  rw [Sums_R_eq hρ, epsP]
  exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)

/-- `p_0 = 0`. -/
private lemma Sums_mom_zero (L : ℝ) : mom L 0 = 0 := by
  ext i
  simp [mom]

/-- `p_{u − v} = p_u − p_v`. -/
private lemma Sums_mom_sub (L : ℝ) (u v : Idx) : mom L (u - v) = mom L u - mom L v := by
  ext i
  simp [mom, mul_sub]

/-- `P = {n ≠ 0 : ε ρ^{1/2} ≤ |p_n|}` for `0 < ρ ≤ 1`. -/
private lemma Sums_inP_iff {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (n : Idx) :
    inP ρ L n ↔ n ≠ 0 ∧ mom L n ∈ {p : R3 | epsP ρ * ρ ^ (1 / 2 : ℝ) ≤ ‖p‖} := by
  have he := Sums_eps_pos hρ
  have hs : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hs1 : ρ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hRe := Sums_R_le_eps hρ hρ1
  have hrR := Sums_r1_le_R hρ hρ1
  constructor
  · intro h
    have hle : epsP ρ * ρ ^ (1 / 2 : ℝ) ≤ ‖mom L n‖ := by
      rcases h with h | h | h
      · exact h.1
      · exact hrR.trans h.1.le
      · exact (mul_le_of_le_one_right he.le hs1).trans h.le
    refine ⟨?_, hle⟩
    rintro rfl
    rw [Sums_mom_zero, norm_zero] at hle
    exact absurd hle (not_le.2 (mul_pos he hs))
  · rintro ⟨-, h⟩
    have h : epsP ρ * ρ ^ (1 / 2 : ℝ) ≤ ‖mom L n‖ := h
    by_cases h1 : ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ)
    · exact Or.inl ⟨h, h1⟩
    · by_cases h2 : ‖mom L n‖ ≤ epsP ρ
      · exact Or.inr (Or.inl ⟨not_le.1 h1, h2⟩)
      · exact Or.inr (Or.inr (not_le.1 h2))

/-- `P_I ∪ P_H = {n ≠ 0 : ε⁻¹ ρ^{1/2} < |p_n|}` for `0 < ρ ≤ 1`. -/
private lemma Sums_inPIH_iff {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (n : Idx) :
    (inPI ρ L n ∨ inPH ρ L n) ↔
      n ≠ 0 ∧ mom L n ∈ {p : R3 | (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) < ‖p‖} := by
  have he := Sums_eps_pos hρ
  have hs : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hRe := Sums_R_le_eps hρ hρ1
  constructor
  · intro h
    have hlt : (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) < ‖mom L n‖ := by
      rcases h with h | h
      · exact h.1
      · exact lt_of_le_of_lt hRe h
    refine ⟨?_, hlt⟩
    rintro rfl
    rw [Sums_mom_zero, norm_zero] at hlt
    exact absurd hlt (not_lt.2 (mul_pos (inv_pos.2 he) hs).le)
  · rintro ⟨-, h⟩
    have h : (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) < ‖mom L n‖ := h
    by_cases h2 : ‖mom L n‖ ≤ epsP ρ
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr (not_le.1 h2)

/-- A function on `Idx` supported in `{|p_n| ≤ R}` is summable. -/
private lemma Sums_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
    (hf : ∀ n, f n ≠ 0 → ‖mom L n‖ ≤ R) : Summable f := by
  have hfin : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
    set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
    refine (Set.finite_Icc (fun _ : Fin 3 => -B) (fun _ => B)).subset ?_
    intro n hn
    have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
      intro i
      have h1 : |(mom L n).ofLp i| ≤ R := by
        have := PiLp.norm_apply_le (mom L n) i
        rw [Real.norm_eq_abs] at this
        exact this.trans hn
      have e : (mom L n).ofLp i = 2 * π / L * (n i : ℝ) := rfl
      rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
      have h2 : |(n i : ℝ)| ≤ L * R / (2 * π) := by
        rw [le_div_iff₀ (by positivity)]
        have := h1
        rw [div_mul_eq_mul_div, div_le_iff₀ hL] at this
        nlinarith
      exact h2.trans (Int.le_ceil _)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 (hi i)).1
      exact_mod_cast this
    · have := (abs_le.1 (hi i)).2
      exact_mod_cast this
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- The `P_L` potential sum with `w_u` in place of `g₀|u|⁻²`, before the rate is evaluated at
`ρ = ρ_N`, `L = L_N`: the main term of the Riemann-sum lemma, plus an error from replacing
`g₀|u|⁻²` by `w_u` on `P_L`. -/
private lemma Sums_PL_pot_core {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧ ∀ ρ L : ℝ, 0 < ρ → ρ ≤ 1 → 0 < L →
      2 * π ≤ L * ρ ^ (1 / 2 : ℝ) → 2 * π ≤ L * ρ ^ (1 / 2 - 1 / 200 : ℝ) →
      |(L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * (∑' n : Idx, if inPL ρ L n then
          lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2) + wmom V w (mom L n) else 0)
        - Section4.G V w| ≤
        K * (ρ ^ (1 / 200 : ℝ) + riemannRate 2 (2 * π / (L * ρ ^ (1 / 2 : ℝ)))) +
          K' * ρ ^ (1 / 200 : ℝ) := by
  have hg : 0 < g0 V w := scat_g0_pos hV hw
  obtain ⟨K, hK0, hK⟩ := sum_PL_pot hg
  obtain ⟨Cg, -, hgd⟩ := Bridge_momDecay hV hw (4 : ℝ)
  obtain ⟨K₁, hK₁0, hK₁⟩ := sum_norm_rpow_le (s := 1) (by norm_num : (1 : ℝ) < 3)
  have hgd0 : (ft (gfun V w) 0).re = g0 V w := by
    rw [scat_ft_g_zero]
    simp
  have hCg : 0 ≤ Cg := by
    have h := hgd.bound 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  refine ⟨K, Cg * K₁, hK0, mul_nonneg hCg hK₁0, fun ρ L hρ hρ1 hL0 hL1 hL2 => ?_⟩
  have hR0 : 0 < ρ ^ (1 / 2 - 1 / 200 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hR1 : ρ ^ (1 / 2 - 1 / 200 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hPLb : ∀ n : Idx, inPL ρ L n →
      n ≠ 0 ∧ 0 < ‖mom L n‖ ∧ ‖mom L n‖ ≤ ρ ^ (1 / 2 - 1 / 200 : ℝ) := by
    intro n hn
    have hb : ‖mom L n‖ ≤ ρ ^ (1 / 2 - 1 / 200 : ℝ) := by
      rw [← Sums_R_eq hρ]
      exact hn.2
    have hpos : 0 < ‖mom L n‖ :=
      lt_of_lt_of_le (mul_pos (Sums_eps_pos hρ) (Real.rpow_pos_of_pos hρ _)) hn.1
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [Sums_mom_zero, norm_zero] at hpos
      exact lt_irrefl _ hpos
    exact ⟨hn0, hpos, hb⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : Idx → ℝ, Fm = fun n => if inPL ρ L n then
      lamPL (g0 V w) ρ (mom L n) + g0 V w / ‖mom L n‖ ^ 2 +
        lamPL (g0 V w) ρ (mom L n) ^ 3 * ρ ^ 2 /
          (1 - ρ ^ 2 * lamPL (g0 V w) ρ (mom L n) ^ 2) else 0 := ⟨_, rfl⟩
  obtain ⟨Fe, hFe⟩ : ∃ Fe : Idx → ℝ, Fe = fun n => if inPL ρ L n then
      wmom V w (mom L n) - g0 V w / ‖mom L n‖ ^ 2 else 0 := ⟨_, rfl⟩
  obtain ⟨Fb, hFb⟩ : ∃ Fb : Idx → ℝ, Fb = fun n =>
      if n ≠ 0 ∧ ‖mom L n‖ ≤ ρ ^ (1 / 2 - 1 / 200 : ℝ) then Cg * ‖mom L n‖ ^ (-(1 : ℝ))
      else 0 := ⟨_, rfl⟩
  -- the summand of the pin splits into the main term and the replacement error
  have hpt : ∀ n : Idx, (if inPL ρ L n then
      lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2) + wmom V w (mom L n) else 0) =
      Fm n + Fe n := by
    intro n
    by_cases hn : inPL ρ L n
    · simp only [hFm, hFe, hn, ↓reduceIte]
      have hx := Particles_rho_lam_PL hg hρ hρ1 hn
      rw [lam_of_inPL hn] at hx ⊢
      generalize lamPL (g0 V w) ρ (mom L n) = l at hx ⊢
      have h1 : 0 < 1 + ρ * l :=
        lt_of_lt_of_le (div_pos (Sums_eps_pos hρ) (by positivity)) hx.2
      have h2 : 0 < 1 - (ρ * l) ^ 2 := by nlinarith [mul_pos h1 (neg_pos.2 hx.1)]
      have h3 : 1 - ρ ^ 2 * l ^ 2 ≠ 0 := by
        rw [← mul_pow]
        exact h2.ne'
      rw [mul_pow]
      have hlD : l ^ 3 * ρ ^ 2 = l * (1 - (1 - ρ ^ 2 * l ^ 2)) := by ring
      rw [hlD]
      generalize 1 - ρ ^ 2 * l ^ 2 = D at h3 ⊢
      field_simp
      ring
    · simp only [hFm, hFe, hn, ↓reduceIte, add_zero]
  have hsF : ∀ F : Idx → ℝ, (∀ n, F n ≠ 0 → inPL ρ L n) → Summable F := fun F hF =>
    Sums_summable_ball hL0 F (fun n hn => (hPLb n (hF n hn)).2.2)
  have hFms : Summable Fm := hsF Fm fun n hn => by
    by_contra h
    exact hn (by simp only [hFm, h, ↓reduceIte])
  have hFes : Summable Fe := hsF Fe fun n hn => by
    by_contra h
    exact hn (by simp only [hFe, h, ↓reduceIte])
  have hFbs : Summable Fb :=
    Sums_summable_ball (R := ρ ^ (1 / 2 - 1 / 200 : ℝ)) hL0 Fb fun n hn => by
      by_contra h
      exact hn (by simp only [hFb, h, and_false, ↓reduceIte])
  -- `|Fe| ≤ Fb`: `|w_u − g₀|u|⁻²| ≤ C_g |u|⁻¹` on `P_L`
  have hFeb : ∀ n : Idx, ‖Fe n‖ ≤ Fb n := by
    intro n
    by_cases hn : inPL ρ L n
    · obtain ⟨hn0, hpos, hb⟩ := hPLb n hn
      have hlip := hgd.lip 0 (mom L n) (by simpa using hb.trans hR1)
      simp only [sub_zero, norm_zero, add_zero, Real.one_rpow, mul_one] at hlip
      rw [hgd0] at hlip
      have hq : 0 < ‖mom L n‖ ^ 2 := by positivity
      have e : wmom V w (mom L n) - g0 V w / ‖mom L n‖ ^ 2 =
          ((ft (gfun V w) (mom L n)).re - g0 V w) / ‖mom L n‖ ^ 2 := by
        unfold wmom
        ring
      simp only [hFe, hFb, hn, hn0, hb, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      rw [e, Real.norm_eq_abs, abs_div, abs_of_pos hq, div_le_iff₀ hq, Real.rpow_neg_one]
      calc |(ft (gfun V w) (mom L n)).re - g0 V w| ≤ Cg * ‖mom L n‖ := hlip
        _ = Cg * ‖mom L n‖⁻¹ * ‖mom L n‖ ^ 2 := by
          field_simp
    · simp only [hFe, hFb, hn, ↓reduceIte, norm_zero]
      split_ifs
      · exact mul_nonneg hCg (Real.rpow_nonneg (norm_nonneg _) _)
      · exact le_rfl
  have hFesum : ‖∑' n, Fe n‖ ≤ ∑' n, Fb n := tsum_of_norm_bounded hFbs.hasSum hFeb
  -- `|Λ|⁻¹ Σ_{P_L} |u|⁻¹ ≤ K₁ R²`
  have hFbsum : (L ^ 3)⁻¹ * ∑' n, Fb n ≤
      Cg * (K₁ * (ρ ^ (1 / 2 - 1 / 200 : ℝ)) ^ (3 - 1 : ℝ)) := by
    have h := hK₁ L (ρ ^ (1 / 2 - 1 / 200 : ℝ)) hR0 hL2
    have e : ∑' n, Fb n = Cg * ∑' n : Idx, (if n ≠ 0 ∧ ‖mom L n‖ ≤ ρ ^ (1 / 2 - 1 / 200 : ℝ)
        then ‖mom L n‖ ^ (-(1 : ℝ)) else 0) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      simp only [hFb]
      split_ifs <;> simp
    rw [e, ← mul_assoc, mul_comm (L ^ 3)⁻¹, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hCg
  -- the exponent: `ρ^{-1/2} R² ≤ ρ^{1/200}`
  have hrem : ρ ^ (-(1 / 2 : ℝ)) * (ρ ^ (1 / 2 - 1 / 200 : ℝ)) ^ (3 - 1 : ℝ) ≤
      ρ ^ (1 / 200 : ℝ) := by
    rw [← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hc0 : 0 ≤ (L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) := by positivity
  -- assemble
  have hmain := hK ρ L hρ hρ1 hL1
  have hsplit : (∑' n : Idx, if inPL ρ L n then
      lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2) + wmom V w (mom L n) else 0) =
      (∑' n, Fm n) + (∑' n, Fe n) := by
    rw [tsum_congr hpt]
    exact hFms.tsum_add hFes
  have hY : |(L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * ∑' n, Fe n| ≤ Cg * K₁ * ρ ^ (1 / 200 : ℝ) := by
    rw [abs_mul, abs_of_nonneg hc0, ← Real.norm_eq_abs]
    calc (L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * ‖∑' n, Fe n‖
        ≤ (L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * ∑' n, Fb n := mul_le_mul_of_nonneg_left hFesum hc0
      _ = ρ ^ (-(1 / 2 : ℝ)) * ((L ^ 3)⁻¹ * ∑' n, Fb n) := by ring
      _ ≤ ρ ^ (-(1 / 2 : ℝ)) * (Cg * (K₁ * (ρ ^ (1 / 2 - 1 / 200 : ℝ)) ^ (3 - 1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hFbsum (Real.rpow_nonneg hρ.le _)
      _ = Cg * K₁ * (ρ ^ (-(1 / 2 : ℝ)) * (ρ ^ (1 / 2 - 1 / 200 : ℝ)) ^ (3 - 1 : ℝ)) := by ring
      _ ≤ Cg * K₁ * ρ ^ (1 / 200 : ℝ) := mul_le_mul_of_nonneg_left hrem (mul_nonneg hCg hK₁0)
  have hsplit2 : (L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * (∑' n : Idx, if inPL ρ L n then
      lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2) + wmom V w (mom L n) else 0) -
        Section4.G V w =
      ((L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * (∑' n : Idx, Fm n) - g0 V w ^ (3 / 2 : ℝ) / π ^ 2) +
        (L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * ∑' n, Fe n := by
    rw [hsplit]
    unfold Section4.G
    ring
  rw [hsplit2]
  refine (abs_add_le _ _).trans ?_
  have hmain' : |(L ^ 3)⁻¹ * ρ ^ (-(1 / 2 : ℝ)) * (∑' n : Idx, Fm n) -
      g0 V w ^ (3 / 2 : ℝ) / π ^ 2| ≤
      K * (ρ ^ (1 / 200 : ℝ) + riemannRate 2 (2 * π / (L * ρ ^ (1 / 2 : ℝ)))) := by
    rw [hFm]
    exact hmain
  linarith

/-- Fact (1) before (7.65) [temp8.73] and (7.20) [temp8.27]: `|ρλ_u| ≤ 1` on `P` for `ρ` small. -/
theorem Pair_rho_lam_le (V w : R3 → ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ u : Idx, inP (rhoN N) (LN N) u →
      |rhoN N * lam V w (rhoN N) (LN N) u| ≤ 1 := by
  have hg1 : 0 ≤ ∫ x, |gfun V w x| := integral_nonneg fun x => abs_nonneg _
  have hsmall : ∀ᶠ N : ℕ in atTop, (∫ x, |gfun V w x|) * rhoN N ^ (1 / 100 : ℝ) ≤ 1 := by
    have h := (Sums_tendsto_rho_pow (by norm_num : (0 : ℝ) < 1 / 100)).const_mul
      (∫ x, |gfun V w x|)
    rw [mul_zero] at h
    exact h.eventually (eventually_le_nhds one_pos)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hsmall.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN u hu => ?_⟩
  obtain ⟨hsm, hN1⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  by_cases hPL : inPL (rhoN N) (LN N) u
  · rw [lam]
    simp only [hPL, ↓reduceIte]
    have hs0 := Real.sqrt_nonneg (1 + 4 * rhoN N * g0 V w / ‖mom (LN N) u‖ ^ 2)
    generalize Real.sqrt (1 + 4 * rhoN N * g0 V w / ‖mom (LN N) u‖ ^ 2) = s at hs0 ⊢
    have hρ0 := hρ.ne'
    have e : rhoN N * ((1 - s) / (1 + s) / rhoN N) = (1 - s) / (1 + s) := by
      field_simp
    rw [e, abs_div, abs_of_pos (by linarith : 0 < 1 + s), div_le_one (by linarith), abs_le]
    constructor <;> linarith
  · have hI : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u := by
      rcases hu with h | h | h
      · exact absurd h hPL
      · exact Or.inl h
      · exact Or.inr h
    have hlam := Particles_lam_abs_le V w (rhoN N) (LN N) u hPL
    have hbig := ((Sums_inPIH_iff (L := LN N) hρ hρ1 u).1 hI).2
    have hbig : (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) < ‖mom (LN N) u‖ := hbig
    have he := Sums_eps_pos hρ
    have hs : 0 < rhoN N ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
    have hsq : rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 2 : ℝ) = rhoN N := by
      rw [← Real.rpow_add hρ]
      norm_num
    have hq : 0 < ‖mom (LN N) u‖ ^ 2 := by
      have : 0 < ‖mom (LN N) u‖ := lt_of_le_of_lt (by positivity) hbig
      positivity
    have hρq : rhoN N ≤ epsP (rhoN N) ^ 2 * ‖mom (LN N) u‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hbig.le 2
      have h2 : epsP (rhoN N) ^ 2 * ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) ^ 2 = rhoN N := by
        have e : epsP (rhoN N) ^ 2 * ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) ^ 2 =
            rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 2 : ℝ) := by
          field_simp
        rw [e, hsq]
      calc rhoN N = epsP (rhoN N) ^ 2 * ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) ^ 2 := h2.symm
        _ ≤ _ := by gcongr
    rw [abs_mul, abs_of_pos hρ]
    calc rhoN N * |lam V w (rhoN N) (LN N) u|
        ≤ rhoN N * ((∫ x, |gfun V w x|) / ‖mom (LN N) u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hlam hρ.le
      _ = (∫ x, |gfun V w x|) * (rhoN N / ‖mom (LN N) u‖ ^ 2) := by ring
      _ ≤ (∫ x, |gfun V w x|) * epsP (rhoN N) ^ 2 :=
          mul_le_mul_of_nonneg_left ((div_le_iff₀ hq).2 hρq) hg1
      _ = (∫ x, |gfun V w x|) * rhoN N ^ (1 / 100 : ℝ) := by rw [Sums_eps_sq hρ.le]
      _ ≤ 1 := hsm

/-- Facts (2) and (5) before (7.65) [temp8.73]: `sup_q |Λ|⁻¹ Σ_{n ≠ 0} |λ_n V_{q − p_n}| ≤ K` and
`|Λ|⁻² Σ_{n, m ≠ 0} |λ_n V_{p_n − p_m} λ_m| ≤ K`. -/
theorem Pair_sum_lamV {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∀ q : R3,
        Summable (fun n : Idx => if n ≠ 0 then
          |lam V w (rhoN N) (LN N) n * (ft V (q - mom (LN N) n)).re| else 0) ∧
        (LN N ^ 3)⁻¹ * (∑' n : Idx, if n ≠ 0 then
          |lam V w (rhoN N) (LN N) n * (ft V (q - mom (LN N) n)).re| else 0) ≤ K) ∧
      Summable (fun nm : Idx × Idx => if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then
          |lam V w (rhoN N) (LN N) nm.1 * (ft V (mom (LN N) (nm.1 - nm.2))).re *
            lam V w (rhoN N) (LN N) nm.2| else 0) ∧
      ((LN N ^ 3) ^ 2)⁻¹ * (∑' nm : Idx × Idx, if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then
          |lam V w (rhoN N) (LN N) nm.1 * (ft V (mom (LN N) (nm.1 - nm.2))).re *
            lam V w (rhoN N) (LN N) nm.2| else 0) ≤ K := by
  obtain ⟨C, hVd, -⟩ := Bridge_momDecay hV hw (4 : ℝ)
  obtain ⟨c, hc⟩ := Bridge_lam_decay hV hw (4 : ℝ)
  obtain ⟨K, hK0, hK⟩ := sum_lam_V_le (le_refl (4 : ℝ)) hVd c
  have hev := Sums_tendsto_rho.eventually hc
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hev.and Sums_eventually_L)
  refine ⟨K, hK0, N₀, fun N hN => ?_⟩
  obtain ⟨hdec, hL⟩ := hN₀ N hN
  obtain ⟨h1, h2, h3⟩ := hK (LN N) (lam V w (rhoN N) (LN N)) hL (fun n hn => hdec (LN N) n hn)
  simp only [Sums_mom_sub]
  exact ⟨h1, h2, h3⟩

/-- (7.23)–(7.24) and (7.68) with `w_u` in place of `g₀|u|⁻²`:
`|Λ|⁻¹ρ^{−1/2} Σ_{u ∈ P_L} (λ_u/(1 − (ρλ_u)²) + w_u) → g₀^{3/2}/π²`, with a rate. -/
theorem Pair_sum_PL_pot {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(LN N ^ 3)⁻¹ * rhoN N ^ (-(1/2 : ℝ)) *
          (∑' n : Idx, if inPL (rhoN N) (LN N) n then
            lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
              wmom V w (mom (LN N) n) else 0)
        - Section4.G V w| ≤ C * rhoN N ^ (1/200 : ℝ) := by
  obtain ⟨K, K', hK0, hK'0, hcore⟩ := Sums_PL_pot_core hV hw
  have hev1 : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ) := by
    filter_upwards [(Sums_tendsto_rho_neg (by norm_num : (0 : ℝ) < 13 / 24)).eventually_ge_atTop
      (2 * π), eventually_ge_atTop 1] with N h1 hN
    rw [Sums_L_mul_rpow hN, show (1 / 2 : ℝ) - 25 / 24 = -(13 / 24) by norm_num]
    exact h1
  have hev2 : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N * rhoN N ^ (1 / 2 - 1 / 200 : ℝ) := by
    filter_upwards [(Sums_tendsto_rho_neg (by norm_num : (0 : ℝ) < 41 / 75)).eventually_ge_atTop
      (2 * π), eventually_ge_atTop 1] with N h1 hN
    rw [Sums_L_mul_rpow hN, show (1 / 2 - 1 / 200 : ℝ) - 25 / 24 = -(41 / 75) by norm_num]
    exact h1
  refine ⟨K * (1 + 3 * (2 * π) ^ (1 / 2 : ℝ)) + K', by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hev1.and (hev2.and (eventually_ge_atTop 1)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, h2, hN1⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, hLpos⟩ := Particles_rhoN_LN hN1
  have h := hcore (rhoN N) (LN N) hρ hρ1 hLpos h1 h2
  have hr := Sums_rate_PL hN1 h1 (b := (1 / 200 : ℝ)) (by norm_num)
  refine h.trans ?_
  have hb : 0 ≤ rhoN N ^ (1 / 200 : ℝ) := Real.rpow_nonneg hρ.le _
  calc K * (rhoN N ^ (1 / 200 : ℝ) +
        riemannRate 2 (2 * π / (LN N * rhoN N ^ (1 / 2 : ℝ)))) + K' * rhoN N ^ (1 / 200 : ℝ)
      ≤ K * (rhoN N ^ (1 / 200 : ℝ) + 3 * (2 * π) ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 200 : ℝ)) +
          K' * rhoN N ^ (1 / 200 : ℝ) := by
        have := mul_le_mul_of_nonneg_left (add_le_add_left hr (rhoN N ^ (1 / 200 : ℝ))) hK0
        linarith
    _ = (K * (1 + 3 * (2 * π) ^ (1 / 2 : ℝ)) + K') * rhoN N ^ (1 / 200 : ℝ) := by ring

/-- `|Λ|⁻¹ Σ_{u ∈ P} V_u w_u → ‖Vw‖₁`, with the rate `ρ^{1/2+η}` (proof of Lemma 4.3 [lemHS2]). -/
theorem Pair_sum_Vw_P {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(LN N ^ 3)⁻¹ * (∑' n : Idx, if inP (rhoN N) (LN N) n then
          (ft V (mom (LN N) n)).re * wmom V w (mom (LN N) n) else 0)
        - normVw V w| ≤ C * rhoN N ^ (1/2 + 1/200 : ℝ) := by
  obtain ⟨C, hVd, hgd⟩ := Bridge_momDecay hV hw (4 : ℝ)
  obtain ⟨K, hK0, hK⟩ := sum_Vw (le_refl (4 : ℝ)) hVd hgd
  refine ⟨K * (1 + 3 * (2 * π) ^ (1 / 2 : ℝ)), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (Sums_eventually_L.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hL, hN1⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hr1 : 0 ≤ epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) :=
    mul_nonneg (Sums_eps_pos hρ).le (Real.rpow_nonneg hρ.le _)
  have hA : IsShell (epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ)) ⊤ 0
      {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖} :=
    ⟨fun p h1 _ => by
      simp only [add_zero] at h1
      exact h1.le, fun p hp => ⟨hp, le_top⟩⟩
  have hAm : MeasurableSet {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖} :=
    measurableSet_le measurable_const measurable_norm
  have h := (hK (LN N) (epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ)) 0 ⊤ _ hL hr1 le_rfl
    ENNReal.zero_lt_top hAm hA).2
  have hsum : (∑' n : Idx, if inP (rhoN N) (LN N) n then
      (ft V (mom (LN N) n)).re * wmom V w (mom (LN N) n) else 0) =
      latSum (LN N) {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖}
        (fun p => (ft V p).re * ((ft (gfun V w) p).re / ‖p‖ ^ 2)) := by
    unfold latSum
    exact tsum_congr fun n => if_congr (Sums_inP_iff hρ hρ1 n) rfl rfl
  rw [hsum, ← Sums_int_Vw hV hw]
  refine h.trans ?_
  have hr := Sums_rate_LN hN1 hL (b := (1 / 2 + 1 / 200 : ℝ)) (by norm_num)
  have e0 : ((⊤ : ENNReal)⁻¹).toReal = 0 := by simp
  rw [e0, Sums_r1_eq hρ]
  have hb : 0 ≤ rhoN N ^ (1 / 2 + 1 / 200 : ℝ) := Real.rpow_nonneg hρ.le _
  calc K * (rhoN N ^ (1 / 2 + 1 / 200 : ℝ) + 0 + 0 + riemannRate 2 (2 * π / LN N))
      ≤ K * (rhoN N ^ (1 / 2 + 1 / 200 : ℝ) +
          3 * (2 * π) ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 2 + 1 / 200 : ℝ)) := by
        gcongr
        linarith
    _ = K * (1 + 3 * (2 * π) ^ (1 / 2 : ℝ)) * rhoN N ^ (1 / 2 + 1 / 200 : ℝ) := by ring

/-- `|Λ|⁻² Σ_{u, v ∈ P} V_{u−v} w_u w_v → ‖Vw²‖₁`, with the rate `ρ^{1/2+η}` ((7.65) [temp8.73]). -/
theorem Pair_sum_Vww_P {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
          if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 then
            (ft V (mom (LN N) (uv.1 - uv.2))).re * wmom V w (mom (LN N) uv.1) *
              wmom V w (mom (LN N) uv.2) else 0)
        - normVw2 V w| ≤ C * rhoN N ^ (1/2 + 1/200 : ℝ) := by
  obtain ⟨C, hVd, hgd⟩ := Bridge_momDecay hV hw (4 : ℝ)
  obtain ⟨K, hK0, hK⟩ := sum_Vww (le_refl (4 : ℝ)) hVd hgd
  refine ⟨K * (1 + 3 * (2 * π) ^ (1 / 2 : ℝ)), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (Sums_eventually_L.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hL, hN1⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hr1 : 0 ≤ epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) :=
    mul_nonneg (Sums_eps_pos hρ).le (Real.rpow_nonneg hρ.le _)
  have hA : IsShell (epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ)) ⊤ 0
      {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖} :=
    ⟨fun p h1 _ => by
      simp only [add_zero] at h1
      exact h1.le, fun p hp => ⟨hp, le_top⟩⟩
  have hAm : MeasurableSet {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖} :=
    measurableSet_le measurable_const measurable_norm
  have h := (hK (LN N) (epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ)) 0 ⊤ _ hL hr1 le_rfl
    ENNReal.zero_lt_top hAm hA).2
  have hsum : (∑' uv : Idx × Idx,
      if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 then
        (ft V (mom (LN N) (uv.1 - uv.2))).re * wmom V w (mom (LN N) uv.1) *
          wmom V w (mom (LN N) uv.2) else 0) =
      latSum2 (LN N) {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖}
        (fun p q => (ft V (p - q)).re * ((ft (gfun V w) p).re / ‖p‖ ^ 2) *
          ((ft (gfun V w) q).re / ‖q‖ ^ 2)) := by
    unfold latSum2
    refine tsum_congr fun nm => ?_
    have hiff : (inP (rhoN N) (LN N) nm.1 ∧ inP (rhoN N) (LN N) nm.2) ↔
        (nm.1 ≠ 0 ∧ nm.2 ≠ 0 ∧
          mom (LN N) nm.1 ∈ {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖} ∧
          mom (LN N) nm.2 ∈ {p : R3 | epsP (rhoN N) * rhoN N ^ (1 / 2 : ℝ) ≤ ‖p‖}) := by
      rw [Sums_inP_iff hρ hρ1, Sums_inP_iff hρ hρ1]
      tauto
    refine if_congr hiff ?_ rfl
    rw [Sums_mom_sub]
    rfl
  rw [hsum, ← Sums_int_Vww hV hw]
  refine h.trans ?_
  have hr := Sums_rate_LN hN1 hL (b := (1 / 2 + 1 / 200 : ℝ)) (by norm_num)
  have e0 : ((⊤ : ENNReal)⁻¹).toReal = 0 := by simp
  rw [e0, Sums_r1_eq hρ]
  have hb : 0 ≤ rhoN N ^ (1 / 2 + 1 / 200 : ℝ) := Real.rpow_nonneg hρ.le _
  calc K * (rhoN N ^ (1 / 2 + 1 / 200 : ℝ) + 0 + 0 + riemannRate 2 (2 * π / LN N))
      ≤ K * (rhoN N ^ (1 / 2 + 1 / 200 : ℝ) +
          3 * (2 * π) ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 2 + 1 / 200 : ℝ)) := by
        gcongr
        linarith
    _ = K * (1 + 3 * (2 * π) ^ (1 / 2 : ℝ)) * rhoN N ^ (1 / 2 + 1 / 200 : ℝ) := by ring

/-- (7.67) [temp8.75]: `||Λ|⁻¹ Σ_{v ∈ P_I ∪ P_H} V_{u−v} w_v − ‖Vw‖₁| ≤ Cρ^{1/2−η}` for `u ∈ P_L`. -/
theorem Pair_sum_Vshift_P {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      |(LN N ^ 3)⁻¹ * (∑' v : Idx,
          if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
            (ft V (mom (LN N) (u - v))).re * wmom V w (mom (LN N) v) else 0)
        - normVw V w| ≤ C * rhoN N ^ (1/2 - 1/200 : ℝ) := by
  obtain ⟨C, hVd, hgd⟩ := Bridge_momDecay hV hw (4 : ℝ)
  have hVe : ∀ p : R3, (ft V (-p)).re = (ft V p).re := fun p => by rw [scat_ft_V_neg hV p]
  obtain ⟨K, hK0, hK⟩ := sum_Vshift_w_near (le_refl (4 : ℝ)) hVd hgd hVe
  refine ⟨K * (2 + 3 * (2 * π) ^ (1 / 2 : ℝ)), by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (Sums_eventually_L.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN u hu => ?_⟩
  obtain ⟨hL, hN1⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hR0 : 0 ≤ (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) :=
    mul_nonneg (inv_nonneg.2 (Sums_eps_pos hρ).le) (Real.rpow_nonneg hρ.le _)
  have hA : IsShell ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) ⊤ 0
      {p : R3 | (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) < ‖p‖} :=
    ⟨fun p h1 _ => by
      simp only [add_zero] at h1
      exact h1, fun p hp => ⟨hp.le, le_top⟩⟩
  have hAm : MeasurableSet {p : R3 | (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) < ‖p‖} :=
    measurableSet_lt measurable_const measurable_norm
  have h := (hK (mom (LN N) u) (LN N) ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) 0 ⊤ _ hL hR0
    le_rfl ENNReal.zero_lt_top hAm hA)
  have hsum : (∑' v : Idx, if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
      (ft V (mom (LN N) (u - v))).re * wmom V w (mom (LN N) v) else 0) =
      latSum (LN N) {p : R3 | (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) < ‖p‖}
        (fun p => (ft V (mom (LN N) u - p)).re * ((ft (gfun V w) p).re / ‖p‖ ^ 2)) := by
    unfold latSum
    refine tsum_congr fun v => if_congr (Sums_inPIH_iff hρ hρ1 v) ?_ rfl
    rw [Sums_mom_sub]
    rfl
  rw [hsum, ← Sums_int_Vw hV hw]
  refine h.trans ?_
  have hr := Sums_rate_LN hN1 hL (b := (1 / 2 - 1 / 200 : ℝ)) (by norm_num)
  have e0 : ((⊤ : ENNReal)⁻¹).toReal = 0 := by simp
  have huR : ‖mom (LN N) u‖ ≤ rhoN N ^ (1 / 2 - 1 / 200 : ℝ) := by
    rw [← Sums_R_eq hρ]
    exact hu.2
  rw [e0, Sums_R_eq hρ]
  have hb : 0 ≤ rhoN N ^ (1 / 2 - 1 / 200 : ℝ) := Real.rpow_nonneg hρ.le _
  calc K * (‖mom (LN N) u‖ + rhoN N ^ (1 / 2 - 1 / 200 : ℝ) + 0 + 0 +
        riemannRate 2 (2 * π / LN N))
      ≤ K * (rhoN N ^ (1 / 2 - 1 / 200 : ℝ) + rhoN N ^ (1 / 2 - 1 / 200 : ℝ) +
          3 * (2 * π) ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 2 - 1 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0
    _ = K * (2 + 3 * (2 * π) ^ (1 / 2 : ℝ)) * rhoN N ^ (1 / 2 - 1 / 200 : ℝ) := by ring

end LHYUpper
