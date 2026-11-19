import LHYUpper.Fock.Expect
import LHYUpper.Scattering.Solution
import LHYUpper.Particles.Lower
import LHYUpper.Particles.Lemma55

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Paper forms of Theorem 5.1 and Lemmas 5.3 and 5.6

States the results of §5 in the form of the paper: Theorem 5.1 [thmA] in the limit form `lim_{k_c→∞}
lim_{ρ→0}` along `ρ = ρ_N` (`Thm5_1_lim`), Lemma 5.3 [boundspsi0] with (5.12) [boundspsi01]
(`Lemma5_3_paper`), and Lemma 5.6 [boundspsi02] (`Lemma5_6_paper`), deduced from the quantitative
bounds of the particle-number estimates. -/

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma PF_rho_pow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.comp hT

/-- `c ρ_N^a ≤ b` for all large `N`, when `a > 0` and `b > 0`. -/
private lemma PF_eventually_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, c * rhoN N ^ a ≤ b := by
  have h : Tendsto (fun N : ℕ => c * rhoN N ^ a) atTop (𝓝 (c * 0)) :=
    (PF_rho_pow_tendsto ha).const_mul c
  exact h.eventually (eventually_le_nhds (by simpa using hb))

/-- `Q_Ψ(n) ≥ 0`, the summands being `|Ψ|²` times nonnegative occupation numbers. -/
private lemma PF_Q_nonneg (Ψ : Occ → ℂ) (n : Idx) : 0 ≤ Expect.Q Ψ [n] := by
  unfold Expect.Q
  refine tsum_nonneg fun α => ?_
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  positivity

/-- Algebra of Lemma 5.6 [boundspsi02]: from `|A - a²| ≤ D ≤ (ε/2) r⁵`, `a ≥ r²/2`, `ε r ≤ 1/4`
one gets `(a - ε r³)² ≤ A ≤ (a + ε r³)²`. -/
private lemma PF_alg {r ε a A D : ℝ} (hr : 0 < r) (hε : 0 < ε) (ha : r ^ 2 / 2 ≤ a)
    (hεr : ε * r ≤ 1 / 4) (hD : D ≤ ε / 2 * r ^ 5) (hA : |A - a ^ 2| ≤ D) :
    (a + -ε * r ^ 3) ^ 2 ≤ A ∧ A ≤ (a + ε * r ^ 3) ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 (hA.trans hD)
  have hr5 : 0 ≤ ε * r ^ 5 := by positivity
  have e1 : 0 ≤ ε * r ^ 3 * (a - r ^ 2 / 2) :=
    mul_nonneg (by positivity) (sub_nonneg.2 ha)
  have e2 : ε * r * (ε * r ^ 5) ≤ 1 / 4 * (ε * r ^ 5) := mul_le_mul_of_nonneg_right hεr hr5
  constructor
  · nlinarith
  · nlinarith

/-- Theorem 5.1 [thmA] in the limit form `lim_{k_c→∞} lim_{ρ→0}`, along `ρ = ρ_N`. -/
theorem Thm5_1_lim {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    (∀ kc : ℝ, Tendsto (fun N : ℕ => rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
        (∑' n : Idx, (if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))) atTop (𝓝 0)) ∧
    (∀ kc : ℝ, Tendsto (fun N : ℕ => rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
        (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))) atTop
        (𝓝 (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2)))) ∧
    Tendsto (fun kc : ℝ => limUnder atTop (fun N : ℕ => rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
        (∑' n : Idx, (if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)))) atTop (𝓝 0) ∧
    Tendsto (fun kc : ℝ => limUnder atTop (fun N : ℕ => rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
        (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)))) atTop
        (𝓝 (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2))) := by
  obtain ⟨C, hC, N₀, h⟩ := Thm5_1 (scat_g0_pos hV hw)
  have hT1 : Tendsto (fun N : ℕ => C * rhoN N ^ (1/200 : ℝ)) atTop (𝓝 0) := by
    simpa using (PF_rho_pow_tendsto (a := 1/200) (by norm_num)).const_mul C
  have hT2 : Tendsto (fun N : ℕ => C * rhoN N ^ (1/400 : ℝ)) atTop (𝓝 0) := by
    simpa using (PF_rho_pow_tendsto (a := 1/400) (by norm_num)).const_mul C
  have h1 : ∀ kc : ℝ, Tendsto (fun N : ℕ => rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
        (∑' n : Idx, (if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))) atTop (𝓝 0) := by
    intro kc
    refine squeeze_zero' ?_ ?_ hT1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
      refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hρ.le _) (by positivity)) ?_
      exact tsum_nonneg fun n => by
        split_ifs
        · exact PF_Q_nonneg _ _
        · exact le_rfl
    · filter_upwards [eventually_ge_atTop N₀] with N hN
      exact (h N hN kc).1
  have h2 : ∀ kc : ℝ, Tendsto (fun N : ℕ => rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
        (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0))) atTop
        (𝓝 (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2))) := by
    intro kc
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' ?_ ?_ hT2)
    · exact Eventually.of_forall fun N => norm_nonneg _
    · filter_upwards [eventually_ge_atTop N₀] with N hN
      rw [Real.norm_eq_abs]
      exact (h N hN kc).2
  refine ⟨h1, h2, ?_, ?_⟩
  · exact (tendsto_congr fun kc => ((h1 kc).limUnder_eq).symm).1 tendsto_const_nhds
  · exact (tendsto_congr fun kc => ((h2 kc).limUnder_eq).symm).1 tendsto_const_nhds

/-- Lemma 5.3 [boundspsi0], (5.12) [boundspsi01]: `|Λ|ρ_{−ε} ≤ Q_Ψ(0) ≤ |Λ|ρ_ε` for `ρ` small. -/
theorem Lemma5_3_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      LN N ^ 3 * rhoEps (g0 V w) (rhoN N) (-ε) ≤ Expect.Q (trialState V w kc N) [0] ∧
        Expect.Q (trialState V w kc N) [0] ≤ LN N ^ 3 * rhoEps (g0 V w) (rhoN N) ε := by
  intro ε hε
  obtain ⟨C, hC, N₁, h⟩ := Lemma5_3 (scat_g0_pos hV hw)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (PF_eventually_le (c := C) (a := 1/400) (by norm_num) hε)
  refine ⟨max (max N₁ N₂) 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hs : 0 < rhoN N ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hb := h N hN₁ kc
  have e : rhoN N ^ (3/2 + 1/400 : ℝ) = rhoN N ^ (3/2 : ℝ) * rhoN N ^ (1/400 : ℝ) :=
    Real.rpow_add hρ _ _
  have hc : C * rhoN N ^ (3/2 + 1/400 : ℝ) ≤ ε * rhoN N ^ (3/2 : ℝ) := by
    rw [e]
    have := hN₂ N hN₂'
    nlinarith
  obtain ⟨hl, hu⟩ := abs_le.1 (hb.trans hc)
  have hl' : rho0 (g0 V w) (rhoN N) - ε * rhoN N ^ (3/2 : ℝ) ≤
      Expect.Q (trialState V w kc N) [0] / LN N ^ 3 := by linarith
  have hu' : Expect.Q (trialState V w kc N) [0] / LN N ^ 3 ≤
      rho0 (g0 V w) (rhoN N) + ε * rhoN N ^ (3/2 : ℝ) := by linarith
  rw [le_div_iff₀ hL3] at hl'
  rw [div_le_iff₀ hL3] at hu'
  unfold rhoEps
  constructor <;> nlinarith

/-- Lemma 5.6 [boundspsi02]: `(|Λ|ρ_{−ε})² ≤ Q_Ψ(0, 0) ≤ (|Λ|ρ_ε)²` for `ρ` small. -/
theorem Lemma5_6_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3 * rhoEps (g0 V w) (rhoN N) (-ε)) ^ 2 ≤ Expect.Q (trialState V w kc N) [0, 0] ∧
        Expect.Q (trialState V w kc N) [0, 0] ≤ (LN N ^ 3 * rhoEps (g0 V w) (rhoN N) ε) ^ 2 := by
  intro ε hε
  have hg := scat_g0_pos hV hw
  obtain ⟨C, hC, N₁, h⟩ := Lemma5_6 hg
  set κ : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (PF_eventually_le (c := κ) (a := 1/2) (by norm_num)
    (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (PF_eventually_le (c := ε) (a := 1/2) (by norm_num)
    (by norm_num : (0 : ℝ) < 1/4))
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 (PF_eventually_le (c := C) (a := 1/400) (by norm_num)
    (half_pos hε))
  refine ⟨max (max (max (max N₁ N₂) N₃) N₄) 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN' : max (max (max N₁ N₂) N₃) N₄ ≤ N := le_of_max_le_left hN
  have hN₁ : N₁ ≤ N := by omega
  have hN₂' : N₂ ≤ N := by omega
  have hN₃' : N₃ ≤ N := by omega
  have hN₄' : N₄ ≤ N := by omega
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  set r : ℝ := rhoN N ^ (1/2 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  set t : ℝ := rhoN N ^ (1/400 : ℝ) with ht
  have hpow : ∀ k : ℕ, ∀ a : ℝ, a = k / 2 → rhoN N ^ a = r ^ k := by
    intro k a ha
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ha]
    congr 1
    ring
  have h2 : rhoN N = r ^ 2 := by
    have := hpow 2 1 (by norm_num)
    simpa using this
  have h3 : rhoN N ^ (3/2 : ℝ) = r ^ 3 := hpow 3 _ (by norm_num)
  have h5 : rhoN N ^ (5/2 + 1/400 : ℝ) = r ^ 5 * t := by
    rw [Real.rpow_add hρ, hpow 5 (5/2) (by norm_num)]
  have hρ0 : rho0 (g0 V w) (rhoN N) = r ^ 2 - κ * r ^ 3 := by
    rw [rho0, h3, ← h2]
  have hκr : κ * r ≤ 1 / 2 := by simpa [hr] using hN₂ N hN₂'
  have hεr : ε * r ≤ 1 / 4 := by simpa [hr] using hN₃ N hN₃'
  have hCt : C * t ≤ ε / 2 := by simpa [ht] using hN₄ N hN₄'
  have ha : r ^ 2 / 2 ≤ rho0 (g0 V w) (rhoN N) := by
    rw [hρ0]
    nlinarith [mul_le_mul_of_nonneg_left hκr (pow_nonneg hr0.le 2)]
  have hL3 : 0 < (LN N ^ 3) ^ 2 := by positivity
  have hb := h N hN₁ kc
  rw [h5] at hb
  have hD : C * (r ^ 5 * t) ≤ ε / 2 * r ^ 5 := by
    have := mul_le_mul_of_nonneg_right hCt (pow_nonneg hr0.le 5)
    nlinarith
  obtain ⟨hlo, hup⟩ := PF_alg hr0 hε ha hεr hD hb
  have hQ : Expect.Q (trialState V w kc N) [0, 0] =
      Expect.Q (trialState V w kc N) [0, 0] / (LN N ^ 3) ^ 2 * (LN N ^ 3) ^ 2 := by
    field_simp
  unfold rhoEps
  rw [h3, mul_pow, mul_pow]
  constructor
  · rw [hQ]
    nlinarith
  · rw [hQ]
    nlinarith

end LHYUpper
